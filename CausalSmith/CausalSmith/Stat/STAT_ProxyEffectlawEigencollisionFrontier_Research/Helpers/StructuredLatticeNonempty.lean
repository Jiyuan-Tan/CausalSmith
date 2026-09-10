import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.StructuredLatticeEnumeration

/-!
# A canonical point in the paper's structured lattice

The exhaustive search is nonempty for every core-domain parameter tuple.  The witness uses the
first `k` coordinate vectors, the identity coordinate matrix, zero effects, and an integer-simplex
weight vector with the required floor.
-/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open Set
open Causalean.Mathlib.Analysis
open scoped Matrix.Norms.L2Operator

noncomputable section

private def canonicalGridBasis {k dx : ℕ} (hkx : k ≤ dx) : RectMatrix dx k :=
  fun i j => if i = Fin.castLE hkx j then 1 else 0

private lemma canonicalGridBasis_orthonormal {k dx : ℕ} (hkx : k ≤ dx) (i j : Fin k) :
    ∑ a, canonicalGridBasis hkx a i * canonicalGridBasis hkx a j =
      if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    rw [Finset.sum_eq_single (Fin.castLE hkx i)]
    · simp [canonicalGridBasis]
    · intro b _ hb
      simp [canonicalGridBasis, hb]
    · simp
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro a _
    by_cases hai : a = Fin.castLE hkx i
    · subst a
      simp [canonicalGridBasis, hij]
    · simp [canonicalGridBasis, hai]

private noncomputable def canonicalSignalBasis {k dx : ℕ} (hkx : k ≤ dx) : SignalBasis dx k :=
  ⟨canonicalGridBasis hkx, canonicalGridBasis_orthonormal hkx⟩

private lemma canonicalGridBasis_signalMin {k dx : ℕ} (hk : 0 < k) (hkx : k ≤ dx) :
    1 ≤ signalMinSingular (canonicalGridBasis hkx) := by
  let V := canonicalSignalBasis hkx
  apply le_singularValues_of_subspace
      (Matrix.toEuclideanLin V.V) ⊤ (by norm_num)
  · simpa using hk
  · intro x _hx
    have hn := (signalBasisLinearIsometry V).norm_map x
    rw [one_mul]
    exact hn.symm.le

private lemma identity_signalMin {k : ℕ} (hk : 0 < k) :
    1 ≤ signalMinSingular (1 : RectMatrix k k) := by
  apply le_singularValues_of_subspace
      (Matrix.toEuclideanLin (1 : RectMatrix k k)) ⊤ (by norm_num)
  · simpa using hk
  · intro x _hx
    simpa [Matrix.toEuclideanLin_apply]

private lemma identity_matrixCLM_norm_le_one {k : ℕ} :
    ‖matrixCLM (1 : RectMatrix k k)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa [matrixCLM, Matrix.toEuclideanLin_apply]

private lemma lattice_floor_numerators
    {k dx n : ℕ} {pi0 sigma0 : ℝ} (hk : 2 ≤ k)
    (hpi : 0 < pi0) (hpiMax : pi0 ≤ 1 / (2 * k : ℝ)) :
    ∃ a : Fin k → ℕ,
      (∀ u, ⌈pi0 * latticeHeight k dx n pi0 sigma0⌉₊ ≤ a u) ∧
      ∑ u, a u = latticeHeight k dx n pi0 sigma0 := by
  let H := latticeHeight k dx n pi0 sigma0
  let ell := ⌈pi0 * H⌉₊
  have hkpos : 0 < k := by omega
  have hH : 2 * k ≤ H := by
    dsimp [H, latticeHeight]
    omega
  have hkpi : (k : ℝ) * pi0 ≤ 1 / 2 := by
    calc
      (k : ℝ) * pi0 ≤ (k : ℝ) * (1 / (2 * k : ℝ)) := by gcongr
      _ = 1 / 2 := by field_simp
  have hellReal : (ell : ℝ) < pi0 * H + 1 := by
    exact Nat.ceil_lt_add_one (mul_nonneg hpi.le (Nat.cast_nonneg H))
  have hkellReal : ((k * ell : ℕ) : ℝ) ≤ H := by
    calc
      ((k * ell : ℕ) : ℝ) = (k : ℝ) * (ell : ℝ) := by norm_num
      _ ≤ (k : ℝ) * (pi0 * H + 1) :=
        (mul_le_mul_of_nonneg_left hellReal.le (Nat.cast_nonneg k))
      _ = ((k : ℝ) * pi0) * H + k := by ring
      _ ≤ (1 / 2) * H + k := by gcongr
      _ ≤ H := by
        have hHreal : ((2 * k : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
        norm_num at hHreal ⊢
        linarith
  have hkell : k * ell ≤ H := by exact_mod_cast hkellReal
  let u0 : Fin k := ⟨0, hkpos⟩
  let surplus := H - k * ell
  let a : Fin k → ℕ := fun u => ell + if u = u0 then surplus else 0
  refine ⟨a, ?_, ?_⟩
  · intro u
    dsimp [a, ell, H]
    omega
  · simp [a, surplus, u0, Finset.sum_add_distrib, H]
    omega

/-- The core-domain inequalities guarantee that the prescribed structured lattice is nonempty. -/
theorem structuredLatticeWellFormed_nonempty
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hpiMax : pi0 ≤ 1 / (2 * k : ℝ))
    (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1) :
    Nonempty {θ : StructuredLatticePoint k dx (effectRadius dz L sigma0) //
      θ.WellFormed (dz := dz) (n := n) (L := L) (pi0 := pi0) (sigma0 := sigma0)} := by
  classical
  let H := latticeHeight k dx n pi0 sigma0
  have hH : 0 < H := by
    have : 2 * k ≤ H := by dsimp [H, latticeHeight]; omega
    omega
  let G := canonicalGridBasis hkx
  have hG : 1 / 2 ≤ signalMinSingular G :=
    (by norm_num : (1 : ℝ) / 2 ≤ 1).trans (canonicalGridBasis_signalMin (by omega) hkx)
  let V := prescribedPolarFactor G hG
  let R : RectMatrix k k := 1
  obtain ⟨a, haFloor, haSum⟩ := lattice_floor_numerators
    (dx := dx) (n := n) (sigma0 := sigma0) hk hpi hpiMax
  let weight : Fin k → ℝ := fun u => a u / H
  let effect : Fin k → ℝ := fun _ => 0
  have hradius : 0 ≤ effectRadius dz L sigma0 := by
    unfold effectRadius
    positivity
  have hlaw : AtomicLaw.Valid (⟨weight, effect⟩ :
      AtomicLaw k (effectRadius dz L sigma0)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro u
      dsimp [weight]
      positivity
    · dsimp [weight]
      rw [← Finset.sum_div]
      have haSumReal : (∑ i, (a i : ℝ)) = (H : ℝ) := by exact_mod_cast haSum
      rw [haSumReal]
      exact div_self (by exact_mod_cast hH.ne')
    · intro u
      exact ⟨by simpa [effect] using neg_nonpos.mpr hradius,
        by simpa [effect] using hradius⟩
  let θ : StructuredLatticePoint k dx (effectRadius dz L sigma0) :=
    ⟨G, V, R, weight, effect, hlaw⟩
  refine ⟨⟨θ, ?_⟩⟩
  dsimp [StructuredLatticePoint.WellFormed]
  refine ⟨?_, ⟨hG, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    by_cases hij : i = Fin.castLE hkx j
    · refine ⟨H, ?_, by simp [θ, G, canonicalGridBasis, hij]⟩
      simp [θ, G, canonicalGridBasis, hij, latticeMesh, H, hH.ne']
    · refine ⟨0, ?_, by simp [θ, G, canonicalGridBasis, hij]⟩
      simp [θ, G, canonicalGridBasis, hij]
  · intro i j
    have hp := prescribedPolarFactor_transpose_mul_self G hG
    have hpij := congrArg (fun M : RectMatrix k k => M i j) hp
    simpa [θ, V, Matrix.mul_apply, Matrix.one_apply] using hpij
  · intro i j
    by_cases hij : i = j
    · refine ⟨H, ?_⟩
      simp [θ, R, hij, latticeMesh, H, hH.ne']
    · refine ⟨0, ?_⟩
      simp [θ, R, hij]
  · have hident := identity_signalMin (k := k) (by omega)
    nlinarith
  · calc
      ‖matrixCLM θ.R‖ ≤ 1 := by simpa [θ, R] using identity_matrixCLM_norm_le_one (k := k)
      _ ≤ 2 * Real.sqrt k * L := by
        have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
        have hsqrtSq := Real.sq_sqrt (show (0 : ℝ) ≤ k by positivity)
        have hsqrt : 1 ≤ Real.sqrt k := by nlinarith [Real.sqrt_nonneg (k : ℝ)]
        have hL0 : (0 : ℝ) ≤ L := le_trans (by norm_num) hL
        nlinarith [mul_nonneg (Real.sqrt_nonneg k) hL0]
  · refine ⟨a, ?_, haSum⟩
    intro u
    exact ⟨haFloor u, rfl⟩
  · intro u
    refine ⟨⟨by simpa [θ, effect] using neg_nonpos.mpr hradius,
      by simpa [θ, effect] using hradius⟩, 0, ?_⟩
    simp [θ, effect]

/-- The core domain therefore supplies the exact exhaustive, lex-ordered search and its
smallest-index empirical minimizer. -/
theorem structuredLatticeSearch_exists
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hpiMax : pi0 ≤ 1 / (2 * k : ℝ))
    (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1) :
    ∃ (m : ℕ) (candidate : Fin m →
        StructuredLatticePoint k dx (effectRadius dz L sigma0))
      (first : (Fin n → Obs dx dz) → Fin m),
      0 < m ∧
      (∀ i, (candidate i).WellFormed (dz := dz) (n := n) (L := L)
        (pi0 := pi0) (sigma0 := sigma0)) ∧
      (∀ θ : StructuredLatticePoint k dx (effectRadius dz L sigma0),
        θ.WellFormed (dz := dz) (n := n) (L := L) (pi0 := pi0) (sigma0 := sigma0) →
          ∃ i, (candidate i).V = θ.V ∧ (candidate i).R = θ.R ∧
            (candidate i).weight = θ.weight ∧ (candidate i).effect = θ.effect) ∧
      (∀ i j, (candidate i).V = (candidate j).V →
        (candidate i).R = (candidate j).R →
        (candidate i).weight = (candidate j).weight →
        (candidate i).effect = (candidate j).effect → i = j) ∧
      (∀ i j, i ≤ j ↔ StructuredLatticePoint.LexLE (candidate i) (candidate j)) ∧
      (∀ sample i, structuredLatticeCriterion (pi0 * sigma0 ^ 2 / 2)
        (empSummary sample) (candidate (first sample)) ≤
          structuredLatticeCriterion (pi0 * sigma0 ^ 2 / 2)
            (empSummary sample) (candidate i)) ∧
      ∀ sample i, structuredLatticeCriterion (pi0 * sigma0 ^ 2 / 2)
        (empSummary sample) (candidate (first sample)) =
          structuredLatticeCriterion (pi0 * sigma0 ^ 2 / 2)
            (empSummary sample) (candidate i) → first sample ≤ i := by
  classical
  obtain ⟨m, candidate, hwf, hcomplete, hinj, horder⟩ :=
    structuredLatticeEnumeration_exists
      (k := k) (dx := dx) (dz := dz) (n := n) (L := L) (pi0 := pi0) (sigma0 := sigma0)
  obtain ⟨θ, hθ⟩ := structuredLatticeWellFormed_nonempty hk hkx hkz hL hpi hpiMax
    hsigma hsigmaMax
  obtain ⟨i, _⟩ := hcomplete θ hθ
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  let score : (Fin n → Obs dx dz) → Fin m → ℝ := fun sample j =>
    structuredLatticeCriterion (pi0 * sigma0 ^ 2 / 2) (empSummary sample) (candidate j)
  obtain ⟨first, hmin, htie⟩ := finite_first_minimizer_exists hm score
  exact ⟨m, candidate, first, hm, hwf, hcomplete, hinj, horder, hmin, htie⟩

end

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
