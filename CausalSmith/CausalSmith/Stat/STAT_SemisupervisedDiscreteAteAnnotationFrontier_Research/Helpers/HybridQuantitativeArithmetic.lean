module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.FactorialCertificate
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridLightBounds
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.PoissonInverseCount

/-! Paper-local deterministic inequalities for the hybrid risk assembly. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open Polynomial

/-- C17, stated for the exact light mean produced by the Poisson calculation.  [the stated conditions](hyp:hP,heps,hB,hL,hcell) [the stated conclusion](goal). -/
lemma light_exact_mean_bias_le {d : Nat} {eps B : Real} {L : Nat}
    (P : DiscreteLaw d) (hP : ModelClass d eps P) (x : Fin d)
    (heps : 0 < eps) (hB : 0 < B) (hL : 2 ≤ L)
    (hcell : cellMass P x ≤ B) :
    |markedMass P x true * (cellMass P x / B) *
          (chebG L).eval (armMass P x true / B) -
        markedMass P x false * (cellMass P x / B) *
          (chebG L).eval (armMass P x false / B) -
        cellMass P x * (outcomeMean P true x - outcomeMean P false x)| ≤
      2 * B / (eps * (L : Real) ^ 2) := by
  let p := cellMass P x
  let s0 := armMass P x false
  let s1 := armMass P x true
  let mu0 := outcomeMean P false x
  let mu1 := outcomeMean P true x
  let e0 := (chebE L).eval (s0 / B)
  let e1 := (chebE L).eval (s1 / B)
  have hp : 0 ≤ p := (cellMass_mem_unitInterval P x).1
  have hs0 : 0 ≤ s0 := Finset.sum_nonneg fun y _ ↦
    (jointMass_mem_unitInterval P x false y).1
  have hs1 : 0 ≤ s1 := Finset.sum_nonneg fun y _ ↦
    (jointMass_mem_unitInterval P x true y).1
  have hs0p : s0 ≤ p := by
    have hsum : s0 + s1 = p := by
      simp [s0, s1, p, armMass, cellMass]
      ring
    linarith
  have hs1p : s1 ≤ p := by
    have hsum : s0 + s1 = p := by
      simp [s0, s1, p, armMass, cellMass]
      ring
    linarith
  by_cases hpzero : p = 0
  · have hs0zero : s0 = 0 := le_antisymm (by simpa [hpzero] using hs0p) hs0
    have hs1zero : s1 = 0 := le_antisymm (by simpa [hpzero] using hs1p) hs1
    have hm0 : markedMass P x false = 0 := by
      rw [markedMass_eq_armMass_mul_outcomeMean]
      simpa [s0] using congrArg (fun z : Real ↦ z * outcomeMean P false x) hs0zero
    have hm1 : markedMass P x true = 0 := by
      rw [markedMass_eq_armMass_mul_outcomeMean]
      simpa [s1] using congrArg (fun z : Real ↦ z * outcomeMean P true x) hs1zero
    have hpx : cellMass P x = 0 := by simpa [p] using hpzero
    simp [hm0, hm1, hpx]
    positivity
  have hppos : 0 < p := lt_of_le_of_ne hp (Ne.symm hpzero)
  have hz0 : s0 / B ∈ Set.Icc (0 : Real) 1 :=
    ⟨div_nonneg hs0 hB.le, (div_le_one hB).2 (hs0p.trans hcell)⟩
  have hz1 : s1 / B ∈ Set.Icc (0 : Real) 1 :=
    ⟨div_nonneg hs1 hB.le, (div_le_one hB).2 (hs1p.trans hcell)⟩
  obtain ⟨_A, _hA, hcert⟩ := chebyshev_factorial_certificate
  rcases (hcert L hL).2.1 (s0 / B) hz0 with ⟨he00, _he01, he0inv, hid0⟩
  rcases (hcert L hL).2.1 (s1 / B) hz1 with ⟨he10, _he11, he1inv, hid1⟩
  have hover0 : eps * p ≤ s0 := by
    simpa [p, s0] using (overlap_armMass_bounds P hP.overlap x false).1
  have hover1 : eps * p ≤ s1 := by
    simpa [p, s1] using (overlap_armMass_bounds P hP.overlap x true).1
  have he0b : e0 ≤ (((L : Real) ^ 2 * (s0 / B))⁻¹) := by
    dsimp [e0]
    exact he0inv (div_pos (lt_of_lt_of_le (mul_pos heps hppos) hover0) hB)
  have he1b : e1 ≤ (((L : Real) ^ 2 * (s1 / B))⁻¹) := by
    dsimp [e1]
    exact he1inv (div_pos (lt_of_lt_of_le (mul_pos heps hppos) hover1) hB)
  have hb := light_cell_bias_abs_le heps hp hB (by omega : 0 < L)
    hover0 hover1 (outcomeMean_mem_unitInterval P false x)
    (outcomeMean_mem_unitInterval P true x) he00 he10 he0b he1b
  have hmarked0 := markedMass_eq_armMass_mul_outcomeMean P x false
  have hmarked1 := markedMass_eq_armMass_mul_outcomeMean P x true
  have hmean := light_mean_error_identity
    (p := p) (B := B) (s0 := s0) (s1 := s1) (mu0 := mu0) (mu1 := mu1)
    (e0 := e0) (e1 := e1) (g0 := (chebG L).eval (s0 / B))
    (g1 := (chebG L).eval (s1 / B))
    (by simp [p, s0, s1, cellMass, armMass]; ring)
    (by simpa [e0] using hid0) (by simpa [e1] using hid1)
  dsimp [p, s0, s1, mu0, mu1, e0, e1] at hb hmean ⊢
  rw [hmarked0, hmarked1]
  rw [hmean]
  simpa [abs_neg] using hb

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
