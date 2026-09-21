module
public import Causalean.Stat.Concentration.Covering.DudleyEntropy.PartB

/-!
# Entropy sums and their integral bound

This file converts the dyadic sum of square-root log covering numbers into a
Riemann integral and chooses the dyadic truncation scale associated with a
positive lower cutoff. These are the analytic estimates used by the final
Dudley entropy theorem.
-/

public section

namespace Causalean.Stat.Concentration

universe v u
open scoped BigOperators
open ProbabilityTheory

section Empirical
variable {Z : Type v}
variable {n m : ℕ} {ι : Type u} [Nonempty ι]
variable {F : ι → Z → ℝ}
variable {S : Fin m → Z}

variable {c : ℝ}
private lemma combine_partA_partB (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (m_pos : 0 < m)
  (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) :
  empiricalRademacherComplexity_without_abs m F S ≤ (ej c n) + 12 / (Real.sqrt m)*(∑ j : Fin n, ((ej c (j+1) - ej c (j+2))*√(Real.log (coveringNumber' h' (ej c (j+1)))))) := by
  apply le_trans (split_main_and_increment_terms cs h' n)
  refine add_le_add ?_ ?_
  · rw [mul_assoc]
    apply inv_mul_le_of_le_mul₀
    · simp
    · apply ej_nonneg c_pos
    · calc
      _ ≤ signs_card_inv m * ∑ (σ : Signs m), ⨆ (fh : ι), (m : ℝ) * (ej c n) := by
        refine inv_mul_le_of_le_mul₀ (by simp) ?_ ?_
        · refine mul_nonneg (by dsimp [signs_card_inv]; simp ) ?_
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          refine mul_nonneg (by simp) ?_
          refine Real.iSup_nonneg' ?_
          simp only [exists_const]
          refine mul_nonneg (by simp) (by apply ej_nonneg c_pos)
        · rw [<- mul_assoc]
          rw [(by
            have : Nonempty (Signs m) := ⟨fun _ => ⟨1, by decide⟩⟩
            exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) :
              (Fintype.card (Signs m) : ℝ) * signs_card_inv m = 1)]
          simp only [one_mul]
          refine Finset.sum_le_sum ?_
          intro i hi
          apply ciSup_mono
          · refine bddAbove_def.mpr ?_
            use m * c
            intro y hy
            simp only [Set.range_const, Set.mem_singleton_iff] at hy
            rw [hy]
            apply mul_le_mul_of_nonneg_left _ (by simp)
            · dsimp [ej]
              refine div_le_self (le_of_lt c_pos) ?_
              · norm_cast
                apply Nat.one_le_pow
                simp
          intro x
          apply partA_sup_bound c_pos h' cs
      _ = signs_card_inv m * ∑ σ, (m : ℝ) * ej c n := by
        repeat apply congrArg
        ext σ
        simp
      _ = signs_card_inv m * ((Fintype.card (Signs m) : ℝ) * ((m : ℝ) * ej c n)) := by
        apply congrArg
        simp
      _ = _ := by
        rw [<- mul_assoc]
        have t : signs_card_inv m * (Fintype.card (Signs m) : ℝ) = 1 := by
          refine inv_mul_cancel₀ ?_
          have : Nonempty (Signs m) := ⟨fun _ => ⟨1, by decide⟩⟩
          exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
        rw [t]
        simp
  · apply le_of_le_of_eq
    · exact partB_bound c_pos h' n m_pos cs
    · rw [Finset.mul_sum]
      apply congrArg
      ext j
      calc
      _ = (ej c ((j : ℕ) + 1) - ej c ((j : ℕ) + 2)) * (6 * (√(4 * Real.log ↑(coveringNumber' h' (ej c ((j : ℕ) + 1)))) / (Real.sqrt m))) := by ring
      _ = ((ej c ((j : ℕ) + 1) - ej c ((j : ℕ) + 2)) * ((12 / (Real.sqrt m)) * √(Real.log ↑(coveringNumber' h' (ej c ((j : ℕ) + 1)))))) := by
        apply congrArg
        calc
        _ = 6 * (2 * √(Real.log ↑(coveringNumber' h' (ej c ((j : ℕ) + 1)))) / (Real.sqrt m)) := by
          apply congrArg
          field_simp
          simp only [Nat.ofNat_nonneg, Real.sqrt_mul, mul_eq_mul_right_iff]
          left
          suffices √(2 * 2) = 2 from by
            rw [<- this]
            rw [Real.sqrt_inj]
            linarith
            linarith
            linarith
          simp
        _ = _ := by ring
      _ = _ := by ring

/-- For a monotone grid and an antitone integrand, a left Riemann term is
bounded by the corresponding interval integral. -/
private theorem MonotoneOn.leftRiemann_sum_le_integral_antitoneOn
    (n : ℕ) (f : ℕ → ℝ) (g : ℝ → ℝ)
    (hf : Monotone f) (hg : AntitoneOn g (Set.Icc (f 0) (f n))) (j : Fin n):
    (f (j+1) - f j) * g (f (j+1)) ≤ ∫ (x : ℝ) in (f j)..(f (j+1)), g x := by
  calc
  _ = ∫ (x : ℝ) in (f j)..(f (j+1)), g (f (j+1)) := by
    simp
  _ ≤ _ := by
    apply intervalIntegral.integral_mono_on
    · apply hf
      simp
    · apply AntitoneOn.intervalIntegrable
      exact antitoneOn_const
    · apply AntitoneOn.intervalIntegrable
      refine antitoneOn_iff_forall_lt.mpr ?_
      intro a ha b hb hab
      apply hg
      · suffices Set.uIcc (f (j : ℕ)) (f ((j : ℕ) + 1)) ⊆ Set.Icc (f 0) (f n) from by
          grind
        refine Set.uIcc_subset_Icc ?_ ?_
        · constructor
          · apply hf
            simp
          · apply hf
            simp
        · constructor
          · apply hf
            simp
          · apply hf
            refine Order.add_one_le_of_lt ?_; simp
      · suffices Set.uIcc (f (j : ℕ)) (f ((j : ℕ) + 1)) ⊆ Set.Icc (f 0) (f n) from by
          grind
        refine Set.uIcc_subset_Icc ?_ ?_
        · constructor
          · apply hf
            simp
          · apply hf
            simp
        · constructor
          · apply hf
            simp
          · apply hf
            refine Order.add_one_le_of_lt ?_; simp
      exact le_of_lt hab
    intro x hx
    simp at hx
    apply hg
    · constructor
      · have : f 0 ≤ f (j : ℕ) := by apply hf; simp
        linarith
      · have : f ((j : ℕ) + 1) ≤ f n := by apply hf; refine Order.add_one_le_of_lt ?_; simp
        linarith
    · constructor
      · apply hf
        simp
      · apply hf
        refine Order.add_one_le_of_lt ?_; simp
    exact hx.2

/-- For an antitone grid and antitone integrand, the full left Riemann sum is
bounded by the interval integral. -/
private theorem AntitoneOn.leftRiemann_sum_le_integral
    (n : ℕ) (f : ℕ → ℝ) (g : ℝ → ℝ)
    (hf : Antitone f) (hg : AntitoneOn g (Set.Icc (f n) (f 0))):
    ∑ j : Fin n, (f j - f (j+1)) * g (f j) ≤ ∫ (x : ℝ) in (f n)..(f 0), g x := by
  by_cases hnpos : 0 < n
  · let h (p : ℕ) := f (n-p)
    have s0 : f n = h 0 := by dsimp [h]
    have s1 : f 0 = h n := by dsimp [h]; simp
    have hh' : Monotone h := by
      dsimp [h]
      change Monotone (f ∘ (fun p ↦ (n - p)))
      apply Antitone.comp
      exact hf
      exact antitone_const_tsub
    rw [s0, s1]
    rw [<- intervalIntegral.sum_integral_adjacent_intervals]
    have t : ∑ j : Fin n, (f (j : ℕ) - f ((j : ℕ) + 1)) * g (f (j : ℕ)) = ∑ j : Fin n, (h ((j : ℕ) + 1) - h (j : ℕ)) * g (h ((j : ℕ) + 1)) := by
      let φ : Fin n ≃ Fin n :=
        { toFun := fun j =>
            ⟨n - 1 - j, by
              have hlt : n - 1 < n := Nat.pred_lt (Nat.ne_of_gt hnpos)
              exact lt_of_le_of_lt (Nat.sub_le _ _) hlt⟩
          invFun := fun j =>
            ⟨n - 1 - j, by
              have hlt : n - 1 < n := Nat.pred_lt (Nat.ne_of_gt hnpos)
              exact lt_of_le_of_lt (Nat.sub_le _ _) hlt⟩
          left_inv := by
            intro j
            apply Fin.ext
            have hjle : (j : ℕ) ≤ n - 1 := Nat.le_pred_of_lt j.is_lt
            have : n - 1 - (n - 1 - j) = j := by grind
            simp [this]
          right_inv := by
            intro j
            apply Fin.ext
            have hjle : (j : ℕ) ≤ n - 1 := Nat.le_pred_of_lt j.is_lt
            have : n - 1 - (n - 1 - j) = j := by grind
            simp [this] }

      have tsum := (Equiv.sum_comp φ (fun j : Fin n => (f j - f (j + 1)) * g (f j)))
      -- simp the rewritten sum to expose `h`
      refine tsum.symm.trans ?_
      refine Finset.sum_congr rfl ?_
      intro j _
      -- unpack φ and h
      change (f (φ j) - f (φ j + 1)) * g (f (φ j)) = (h (j + 1) - h j) * g (h (j + 1))
      dsimp [φ, h]
      -- arithmetic on naturals
      have hjle : (j : ℕ) ≤ n - 1 := Nat.le_pred_of_lt j.is_lt
      simp [Nat.sub_sub, Nat.add_comm]
      left
      apply congrArg
      grind
    rw [t]
    have u : ∑ k ∈ Finset.range n, ∫ (x : ℝ) in h k..h (k + 1), g x = ∑ k : Fin n, ∫ (x : ℝ) in h k..h (k + 1), g x := by
      exact Finset.sum_range fun i ↦ ∫ (x : ℝ) in h i..h (i + 1), g x
    rw [u]
    apply Finset.sum_le_sum
    intro i yi
    apply MonotoneOn.leftRiemann_sum_le_integral_antitoneOn
    · exact hh'
    · rw [<-s0]
      rw [<-s1]
      exact hg
    intro k kn
    apply AntitoneOn.intervalIntegrable
    rw [s0] at hg
    rw [s1] at hg
    apply hg.mono
    refine Set.uIcc_subset_Icc ?_ ?_
    constructor
    · apply hh'
      simp
    · apply hh'
      linarith
    constructor
    · apply hh'
      simp
    · apply hh'
      linarith
  · have n_zero : n = 0 := by linarith
    rw [n_zero]
    simp

private lemma ej_antitone (c_nonneg : 0 ≤ c) : Antitone (fun n : ℕ ↦ ej c n) := by
  dsimp [ej]
  refine Antitone.const_mul ?_ ?_
  refine inv_pow_anti ?_
  norm_num
  exact c_nonneg

/-- For [a function class evaluated on a finite sample](hyp:Z,m,ι,F,S), [a positive empirical
radius](hyp:c), [positivity of that radius](hyp:c_pos), [total boundedness of the empirical
class](hyp:h'), [a terminal chaining level](hyp:n), [positive sample size](hyp:m_pos), and [a
uniform empirical-radius bound](hyp:cs), [the empirical Rademacher complexity is bounded by a
terminal dyadic remainder plus the entropy integral from that scale to half the radius](goal). -/
lemma entropy_sum_to_integral_bound (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (m_pos : 0 < m)
  (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) :
  empiricalRademacherComplexity_without_abs m F S ≤ 2 * (ej c (n+1)) + 12 / (Real.sqrt m)*(∫ (x : ℝ) in (ej c (n+1))..(c/2),√(Real.log (coveringNumber' h' x))) := by
  calc
  _ ≤ (ej c n) + 12 / (Real.sqrt m)*(∑ j : Fin n, ((ej c (j+1) - ej c (j+2))*√(Real.log (coveringNumber' h' (ej c (j+1)))))) := combine_partA_partB c_pos h' n m_pos cs
  _ = 2 * (ej c (n+1)) + 12 / (Real.sqrt m)*(∑ j : Fin n, ((ej c (j+1) - ej c (j+2))*√(Real.log (coveringNumber' h' (ej c (j+1)))))) := by
    refine add_right_cancel_iff.mpr ?_
    dsimp [ej]
    grind
  _ ≤ _ := by
    suffices (∑ j : Fin n, ((ej c (j+1) - ej c (j+2))*√(Real.log (coveringNumber' h' (ej c (j+1)))))) ≤ (∫ (x : ℝ) in (ej c (n + 1))..(c/2),√(Real.log (coveringNumber' h' x))) from by
      refine (add_le_add_iff_left (2 * ej c (n + 1))).mpr ?_
      apply mul_le_mul_of_nonneg_left
      exact this
      refine div_nonneg ?_ ?_
      simp
      simp
    let f := fun (x : ℕ) ↦ ej c (x + 1)
    have : c / 2 = ej c 1 := by
      dsimp [ej]
      simp
    rw [this]
    let g := fun x ↦ √(Real.log ↑(coveringNumber' h' x))
    suffices ∑ j : Fin n, (f j - f (j + 1)) * g (f j) ≤ ∫ (x : ℝ) in f n..f 0, g x from by
      dsimp [f, g] at this
      have p (j : Fin n) : (j : ℕ) + 1 + 1 = (j : ℕ) + 2 := by ring
      apply le_of_eq_of_le rfl
      exact this
    have s : 0 < f n := by
      dsimp [f]
      dsimp [ej]
      simp
      exact c_pos
    apply AntitoneOn.leftRiemann_sum_le_integral
    · dsimp [f]
      refine Antitone.covariant_of_const' ?_ 1
      apply ej_antitone
      apply le_of_lt c_pos
    · dsimp [g]
      have f0 : Monotone (fun x ↦ √x) := by apply Real.sqrt_le_sqrt
      apply Monotone.comp_antitoneOn f0
      refine antitoneOn_iff_forall_lt.mpr ?_
      intro a ha b hb hab
      apply Real.log_le_log
      · apply Nat.cast_pos.mpr
        apply coveringNumber'_nonzero
        · exact e_nonempty
        simp at hb
        linarith
      norm_cast
      apply coveringNumber'_antitone
      simp
      simp at ha
      linarith
      simp
      simp at hb
      linarith
      apply le_of_lt hab

omit [Nonempty ι] in
/-- If [the target scale is positive](hyp:ε_pos) and [smaller than half the initial
radius](hyp:c_ε), then [some dyadic chaining radius lies strictly above the target scale and
at most twice it](goal). -/
lemma choose_dyadic_scale_for_epsilon (ε : ℝ) (ε_pos : 0 < ε) (c_ε : ε < c / 2) :
  ∃ n, (ε < (ej c (n+1))) ∧ ((ej c (n+1)) ≤ 2 * ε) := by
  dsimp [ej]
  suffices ∃ n : ℕ, n < Real.logb 2 (c / ε) ∧ Real.logb 2 (c / ε) ≤ n + 1 from by
    obtain ⟨m0, ⟨hm1, hm2⟩⟩ := this
    rw [Real.logb_le_iff_le_rpow] at hm2
    rw [Real.lt_logb_iff_rpow_lt] at hm1
    have r : 0 < m0 := by
      have r0 : 2 < c / ε := by
        have r00 : 2 * ε < c := by
          refine (lt_div_iff₀' ?_).mp c_ε
          norm_num
        exact (lt_div_iff₀ ε_pos).mpr r00
      have r1 : (2 : ℝ) < (2 : ℝ) ^ (↑m0 + 1) := by
        norm_cast at hm2
        apply lt_of_lt_of_le r0
        norm_cast
      rcases Nat.eq_zero_or_pos m0 with h0 | h0
      · rw [h0] at r1
        norm_num at r1
      · exact h0
    have p0 : ε < c / 2 ^ (↑m0) := by
      have htmp := mul_lt_mul_of_pos_right hm1 ε_pos
      have htmp_mul : ε * 2 ^ (↑m0) < c := by
        field_simp at htmp
        simp at htmp
        rw [mul_comm]
        exact htmp
      have hpowpos : 0 < (2 : ℝ) ^ (↑m0) := pow_pos (by norm_num) _
      have := mul_lt_mul_of_pos_right htmp_mul (inv_pos.mpr hpowpos)
      simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using this
    have p1 : c / 2 ^ (↑m0) ≤ 2 * ε := by
      have htmp : c ≤ ε * 2 ^ (↑m0 + 1) := by
        have := mul_le_mul_of_nonneg_left hm2 (le_of_lt ε_pos)
        field_simp at this
        norm_cast at this
        norm_cast
      have hpowpos : 0 < (2 : ℝ) ^ (↑m0) := pow_pos (by norm_num) _
      have hpow_ne : (2 : ℝ) ^ (↑m0) ≠ 0 := by exact ne_of_gt hpowpos
      calc
        c / 2 ^ (↑m0) = c * ((2 : ℝ) ^ (↑m0))⁻¹ := by
          simp [div_eq_mul_inv]
        _ ≤ (ε * 2 ^ (↑m0 + 1)) * ((2 : ℝ) ^ (↑m0))⁻¹ := by
          exact mul_le_mul_of_nonneg_right htmp (inv_nonneg.mpr (le_of_lt hpowpos))
        _ = ε * 2 := by
          simp [pow_succ, mul_comm, mul_assoc, hpow_ne]
        _ = 2 * ε := by ring
    use (m0 - 1)
    have : m0 - 1 + 1 = m0 := by
      grind
    rw [this]
    exact ⟨p0, p1⟩
    · norm_num
    · field_simp
      linarith
    · norm_num
    · field_simp
      linarith
  use Int.toNat (Int.ceil (Real.logb 2 (c / ε))) - 1
  have h3 : 0 < Real.logb 2 (c / ε) := by
    refine Real.logb_pos (by linarith) ?_
    refine (one_lt_div₀ ε_pos).mpr ?_
    apply lt_trans c_ε
    linarith
  have h2 :
      ((⌈Real.logb 2 (c / ε)⌉ : ℤ) : ℝ) =
      ((⌈Real.logb 2 (c / ε)⌉.toNat : ℕ) : ℝ) := by
        norm_cast
        refine Int.eq_natCast_toNat.mpr ?_
        exact Int.ceil_nonneg (le_of_lt h3)
  have : (1 : ℤ) ≤ ⌈Real.logb 2 (c / ε)⌉ := by
    simpa using Int.one_le_ceil_iff.mpr h3
  have hceil_nonneg : 0 ≤ ⌈Real.logb 2 (c / ε)⌉ := Int.ceil_nonneg (le_of_lt h3)
  have hcast : Int.ofNat (⌈Real.logb 2 (c / ε)⌉.toNat) = ⌈Real.logb 2 (c / ε)⌉ :=
    Int.toNat_of_nonneg hceil_nonneg
  have h_nat : 1 ≤ ⌈Real.logb 2 (c / ε)⌉.toNat := by
    have : (Int.ofNat 1) ≤ Int.ofNat (⌈Real.logb 2 (c / ε)⌉.toNat) := by
      simpa [hcast] using this
    exact (Int.ofNat_le).1 this
  constructor
  · rw [Nat.cast_sub]
    rw [<- h2]
    simp
    rw [<- Int.le_ceil_iff]
    simpa using h_nat
  · norm_cast
    have : ⌈Real.logb 2 (c / ε)⌉.toNat - 1 + 1 = ⌈Real.logb 2 (c / ε)⌉.toNat := by
      exact Nat.sub_add_cancel h_nat
    rw [this]
    rw [<- h2]
    exact Int.le_ceil (Real.logb 2 (c / ε))

end Empirical
end Causalean.Stat.Concentration
