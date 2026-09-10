import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.StructuredLatticeEnumeration

/-! # Polynomial cardinality of the structured lattice -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open scoped Matrix.Norms.L2Operator

noncomputable section

private lemma boundedLatticeInt_card_cast_le (H : ℕ) (B : ℝ)
    (hH : 1 ≤ H) (hB : 0 ≤ B) :
    (Fintype.card (BoundedLatticeInt H B) : ℝ) ≤ (2 * B + 3) * H := by
  have hc0 : (0 : ℤ) ≤ ⌈(H : ℝ) * B⌉ :=
    Int.ceil_nonneg (mul_nonneg (Nat.cast_nonneg H) hB)
  rw [show Fintype.card (BoundedLatticeInt H B) =
      (2 * ⌈(H : ℝ) * B⌉ + 1 : ℤ).toNat by
    simp [BoundedLatticeInt, Int.card_Icc]
    ring_nf]
  have hexpr : (0 : ℤ) ≤ 2 * ⌈(H : ℝ) * B⌉ + 1 := by omega
  have htoR : (((2 * ⌈(H : ℝ) * B⌉ + 1 : ℤ).toNat : ℕ) : ℝ) =
      ((2 * ⌈(H : ℝ) * B⌉ + 1 : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hexpr
  rw [htoR]
  have hc : ((⌈(H : ℝ) * B⌉ : ℤ) : ℝ) < (H : ℝ) * B + 1 :=
    Int.ceil_lt_add_one _
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  push_cast
  nlinarith

private lemma latticeHeight_cast_le_sqrt
    (k dx n : ℕ) (pi0 sigma0 : ℝ) (hn : 1 ≤ n) :
    (latticeHeight k dx n pi0 sigma0 : ℝ) ≤
      (2 + (⌈pi0⁻¹⌉₊ + 2 * k + ⌈4 * Real.sqrt (dx * k)⌉₊ +
        ⌈2 * k / sigma0⌉₊ : ℕ) : ℝ) * Real.sqrt n := by
  let c : ℕ := ⌈pi0⁻¹⌉₊ + 2 * k + ⌈4 * Real.sqrt (dx * k)⌉₊ +
    ⌈2 * k / sigma0⌉₊
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hnR
  have hceil : (⌈Real.sqrt n⌉₊ : ℝ) ≤ 2 * Real.sqrt n := by
    have hlt := Nat.ceil_lt_add_one (Real.sqrt_nonneg (n : ℝ))
    exact (le_of_lt hlt).trans (by linarith)
  have hc : (c : ℝ) ≤ (c : ℝ) * Real.sqrt n := by
    calc
      (c : ℝ) = (c : ℝ) * 1 := by ring
      _ ≤ (c : ℝ) * Real.sqrt n :=
        mul_le_mul_of_nonneg_left hsqrt (Nat.cast_nonneg c)
  calc
    (latticeHeight k dx n pi0 sigma0 : ℝ) = (⌈Real.sqrt n⌉₊ : ℝ) + c := by
      simp [latticeHeight, c]
      ring_nf
    _ ≤ 2 * Real.sqrt n + (c : ℝ) * Real.sqrt n := add_le_add hceil hc
    _ = (2 + (c : ℝ)) * Real.sqrt n := by ring

private lemma sqrt_pow_eq_rpow_half (n D : ℕ) (hn : 1 ≤ n) :
    Real.sqrt n ^ D = Real.rpow (n : ℝ) ((D : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast]
  rw [← Real.rpow_mul (x := (n : ℝ)) (by positivity) (1 / 2) (D : ℝ)]
  congr 1
  ring

/-- For fixed structural parameters, the exact encoder (and hence every prescribed duplicate-free
search) has the paper's `n^(D/2)` cardinality, where `D = dx*k+k^2+2*k-1`. -/
theorem prescribed_candidateCount_polynomial_bound
    (k dx dz : ℕ) (L pi0 sigma0 : ℝ)
    (hk : 2 ≤ k) (_hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (_hpi : 0 < pi0) (_hpiMax : pi0 ≤ 1 / (2 * k : ℝ))
    (hsigma : 0 < sigma0) (_hsigmaMax : sigma0 ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ A : LatticeEstimator k dx dz n (effectRadius dz L sigma0),
        IsPrescribedStructuredLattice (L := L) (pi0 := pi0) (sigma0 := sigma0) A →
        (A.candidateCount : ℝ) ≤ C * Real.rpow (n : ℝ)
          ((dx * k + k ^ 2 + 2 * k - 1 : ℝ) / 2) := by
  let cH : ℝ := 2 + (⌈pi0⁻¹⌉₊ + 2 * k + ⌈4 * Real.sqrt (dx * k)⌉₊ +
    ⌈2 * k / sigma0⌉₊ : ℕ)
  let cR : ℝ := 2 * effectRadius dz L sigma0 + 3
  let cM : ℝ := 4 * Real.sqrt k * L + 3
  let D : ℕ := dx * k + k ^ 2 + 2 * k - 1
  let C : ℝ := 5 ^ (dx * k) * cM ^ (k ^ 2) * 2 ^ (k - 1) * cR ^ k * cH ^ D
  have hdz : 0 < dz := lt_of_lt_of_le (by omega : 0 < k) hkz
  have hcH : 0 < cH := by dsimp [cH]; positivity
  have hcR : 0 < cR := by
    dsimp [cR, effectRadius]
    positivity
  have hcM : 0 < cM := by
    dsimp [cM]
    positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro n hn A hA
  let H := latticeHeight k dx n pi0 sigma0
  have hH : 1 ≤ H := by
    dsimp [H, latticeHeight]
    omega
  have hcode := isPrescribedStructuredLattice_candidateCount_le_code A hA
  have hgrid := boundedLatticeInt_card_cast_le H 1 hH (by norm_num)
  have hcoord := boundedLatticeInt_card_cast_le H (2 * Real.sqrt k * L) hH (by positivity)
  have heffect := boundedLatticeInt_card_cast_le H (effectRadius dz L sigma0) hH (by
    dsimp [effectRadius]
    positivity)
  have hmass : ((H + 1 : ℕ) : ℝ) ≤ 2 * H := by
    exact_mod_cast (by omega : H + 1 ≤ 2 * H)
  have hmass' : (H : ℝ) + 1 ≤ 2 * H := by simpa using hmass
  have hcodeReal :
      (Fintype.card (StructuredLatticeCode k dx H L sigma0
        (effectRadius dz L sigma0)) : ℝ) ≤
        5 ^ (dx * k) * cM ^ (k ^ 2) * 2 ^ (k - 1) * cR ^ k * H ^ D := by
    rw [structuredLatticeCode_card]
    push_cast
    have hD : dx * k + k ^ 2 + (k - 1) + k = dx * k + k ^ 2 + 2 * k - 1 := by omega
    have hgpow : (Fintype.card (BoundedLatticeInt H 1) : ℝ) ^ (dx * k) ≤
        (5 * H) ^ (dx * k) := by
      gcongr
      calc
        (Fintype.card (BoundedLatticeInt H 1) : ℝ) ≤ (2 * 1 + 3) * H := hgrid
        _ = 5 * H := by ring
    have hcpow : (Fintype.card
        (BoundedLatticeInt H (2 * Real.sqrt k * L)) : ℝ) ^ (k ^ 2) ≤
        (cM * H) ^ (k ^ 2) := by
      gcongr
      calc
        (Fintype.card (BoundedLatticeInt H (2 * Real.sqrt k * L)) : ℝ) ≤
            (2 * (2 * Real.sqrt k * L) + 3) * H := hcoord
        _ = cM * H := by simp only [cM]; ring
    have hmpow : ((H + 1 : ℕ) : ℝ) ^ (k - 1) ≤ (2 * H) ^ (k - 1) := by
      gcongr
    have hepow : (Fintype.card
        (BoundedLatticeInt H (effectRadius dz L sigma0)) : ℝ) ^ k ≤
        (cR * H) ^ k := by
      gcongr
    calc
      (Fintype.card (BoundedLatticeInt H 1) : ℝ) ^ (dx * k) *
          (Fintype.card (BoundedLatticeInt H (2 * Real.sqrt k * L)) : ℝ) ^ (k ^ 2) *
          ((H : ℝ) + 1) ^ (k - 1) *
          (Fintype.card (BoundedLatticeInt H (effectRadius dz L sigma0)) : ℝ) ^ k
          ≤ (5 * H) ^ (dx * k) * (cM * H) ^ (k ^ 2) *
            (2 * H) ^ (k - 1) * (cR * H) ^ k := by gcongr
      _ = 5 ^ (dx * k) * cM ^ (k ^ 2) * 2 ^ (k - 1) * cR ^ k * H ^ D := by
        rw [mul_pow, mul_pow, mul_pow, mul_pow]
        rw [show D = dx * k + k ^ 2 + (k - 1) + k by omega,
          pow_add, pow_add, pow_add]
        ring
  have hHeight : (H : ℝ) ≤ cH * Real.sqrt n := by
    exact latticeHeight_cast_le_sqrt k dx n pi0 sigma0 hn
  have hpow : (H : ℝ) ^ D ≤ cH ^ D * Real.sqrt n ^ D := by
    calc
      (H : ℝ) ^ D ≤ (cH * Real.sqrt n) ^ D := by gcongr
      _ = cH ^ D * Real.sqrt n ^ D := mul_pow _ _ _
  have hDform : D = dx * k + k ^ 2 + 2 * k - 1 := rfl
  have hExp : (D : ℝ) / 2 =
      (dx * k + k ^ 2 + 2 * k - 1 : ℝ) / 2 := by
    dsimp [D]
    rw [Nat.cast_sub (by omega : 1 ≤ dx * k + k ^ 2 + 2 * k)]
    push_cast
    ring
  calc
    (A.candidateCount : ℝ) ≤
        (Fintype.card (StructuredLatticeCode k dx H L sigma0
          (effectRadius dz L sigma0)) : ℝ) := by exact_mod_cast hcode
    _ ≤ 5 ^ (dx * k) * cM ^ (k ^ 2) * 2 ^ (k - 1) * cR ^ k * H ^ D := hcodeReal
    _ ≤ 5 ^ (dx * k) * cM ^ (k ^ 2) * 2 ^ (k - 1) * cR ^ k *
        (cH ^ D * Real.sqrt n ^ D) := by gcongr
    _ = C * Real.rpow (n : ℝ) ((dx * k + k ^ 2 + 2 * k - 1 : ℝ) / 2) := by
      rw [sqrt_pow_eq_rpow_half n D hn, hExp]
      simp only [C]
      ring

/-- The charged exhaustive-search runtime obeys the matching polynomial bound. -/
theorem prescribed_latticeOperationCount_polynomial_bound
    (k dx dz : ℕ) (L pi0 sigma0 : ℝ)
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hpiMax : pi0 ≤ 1 / (2 * k : ℝ))
    (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ A : LatticeEstimator k dx dz n (effectRadius dz L sigma0),
        IsPrescribedStructuredLattice (L := L) (pi0 := pi0) (sigma0 := sigma0) A →
        (A.candidateCount : ℝ) ≤ C * Real.rpow (n : ℝ)
          ((dx * k + k ^ 2 + 2 * k - 1 : ℝ) / 2) ∧
        (latticeOperationCount A : ℝ) ≤ C *
          (n + Real.rpow (n : ℝ) ((dx * k + k ^ 2 + 2 * k - 1 : ℝ) / 2)) := by
  obtain ⟨C0, hC0, hbound⟩ := prescribed_candidateCount_polynomial_bound
    k dx dz L pi0 sigma0 hk hkx hkz hL hpi hpiMax hsigma hsigmaMax
  let C := max 1 C0
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro n hn A hA
  have hcand0 := hbound n hn A hA
  have hC0le : C0 ≤ C := le_max_right _ _
  have hrpow : 0 ≤ Real.rpow (n : ℝ)
      ((dx * k + k ^ 2 + 2 * k - 1 : ℝ) / 2) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hcand : (A.candidateCount : ℝ) ≤ C * Real.rpow (n : ℝ)
      ((dx * k + k ^ 2 + 2 * k - 1 : ℝ) / 2) :=
    hcand0.trans (mul_le_mul_of_nonneg_right hC0le hrpow)
  refine ⟨hcand, ?_⟩
  rw [latticeOperationCount, Nat.cast_add]
  calc
    (n : ℝ) + A.candidateCount ≤ (n : ℝ) + C * Real.rpow (n : ℝ)
        ((dx * k + k ^ 2 + 2 * k - 1 : ℝ) / 2) := by
      simpa [add_comm] using add_le_add_right hcand (n : ℝ)
    _ ≤ C * ((n : ℝ) + Real.rpow (n : ℝ)
        ((dx * k + k ^ 2 + 2 * k - 1 : ℝ) / 2)) := by
      have hCone : 1 ≤ C := le_max_left _ _
      calc
        (n : ℝ) + C * Real.rpow (n : ℝ)
            ((dx * k + k ^ 2 + 2 * k - 1 : ℝ) / 2) ≤
            C * n + C * Real.rpow (n : ℝ)
              ((dx * k + k ^ 2 + 2 * k - 1 : ℝ) / 2) := by
          gcongr
          simpa using mul_le_mul_of_nonneg_right hCone (Nat.cast_nonneg n)
        _ = C * ((n : ℝ) + Real.rpow (n : ℝ)
            ((dx * k + k ^ 2 + 2 * k - 1 : ℝ) / 2)) := by ring

end

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
