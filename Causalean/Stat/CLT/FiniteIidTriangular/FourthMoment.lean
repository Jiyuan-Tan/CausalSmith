module
public import Causalean.Stat.CLT.FiniteIidTriangular.Basic

/-!
Fourth-moment bounds for bounded finite iid triangular rows. The module expands the fourth power of a score sum by index pattern and derives a uniform fourth-moment bound for its square-root normalization.
-/

@[expose] public section

namespace Causalean.Stat.CLT.FiniteIidTriangular

/-- An ordered quadruple has a singleton coordinate when some index appears exactly once. -/
def fourthHasSingleton {k : ℕ} (p : Fin 4 → Fin k) : Prop :=
  ∃ i : Fin k, (Finset.univ.filter (fun a : Fin 4 => p a = i)).card = 1

/-- An ordered quadruple is constant when all four of its indices coincide. -/
def fourthConstant {k : ℕ} (p : Fin 4 → Fin k) : Prop :=
  ∀ a, p a = p 0

open Classical in
/-- Quadruples without a singleton contribute either a one-index fourth moment or one
of the three pairings of two distinct indices. -/
theorem fourth_index_sum (k : ℕ) (m₂ m₄ : ℝ) :
    (∑ p : Fin 4 → Fin k,
      if fourthHasSingleton p then (0 : ℝ)
      else if fourthConstant p then m₄ else m₂ ^ 2) =
        (k : ℝ) * m₄ + 3 * (k : ℝ) * ((k : ℝ) - 1) * m₂ ^ 2 := by
  classical
  have hpoint (a b c d : Fin k) :
      (if fourthHasSingleton (![a,b,c,d] : Fin 4 → Fin k) then 0 else
         if fourthConstant ![a,b,c,d] then m₄ else m₂^2) =
      (if a=b ∧ a=c ∧ a=d then m₄ else 0) +
      (if a=b ∧ c=d ∧ a≠c then m₂^2 else 0) +
      (if a=c ∧ b=d ∧ a≠b then m₂^2 else 0) +
      (if a=d ∧ b=c ∧ a≠b then m₂^2 else 0) := by
    have hc : fourthConstant (![a,b,c,d] : Fin 4 → Fin k) ↔
        a=b ∧ a=c ∧ a=d := by
      simp [fourthConstant, Fin.forall_fin_succ, eq_comm]
    have hs : fourthHasSingleton (![a,b,c,d] : Fin 4 → Fin k) ↔
        (a ≠ b ∧ a ≠ c ∧ a ≠ d) ∨ (b ≠ a ∧ b ≠ c ∧ b ≠ d) ∨
        (c ≠ a ∧ c ≠ b ∧ c ≠ d) ∨ (d ≠ a ∧ d ≠ b ∧ d ≠ c) := by
      have hcard : fourthHasSingleton (![a,b,c,d] : Fin 4 → Fin k) ↔
          ∃ i : Fin k, (if a=i then 1 else 0) + (if b=i then 1 else 0) +
            (if c=i then 1 else 0) + (if d=i then 1 else 0) = (1 : ℕ) := by
        simp only [fourthHasSingleton, Finset.card_filter, Fin.sum_univ_four]
        rfl
      rw [hcard]
      constructor
      · rintro ⟨i, hi⟩
        by_cases ha : a = i <;> by_cases hb : b = i <;>
          by_cases hc : c = i <;> by_cases hd : d = i <;>
          simp_all [eq_comm]
      · rintro (h | h | h | h)
        · refine ⟨a, ?_⟩; simp_all [eq_comm]
        · refine ⟨b, ?_⟩; simp_all [eq_comm]
        · refine ⟨c, ?_⟩; simp_all [eq_comm]
        · refine ⟨d, ?_⟩; simp_all [eq_comm]
    rw [hc, hs]
    by_cases h₁ : a = b <;> by_cases h₂ : a = c <;> by_cases h₃ : a = d <;>
      by_cases h₄ : b = c <;> by_cases h₅ : b = d <;> by_cases h₆ : c = d <;>
      simp_all [eq_comm]
  have hquad (f : (Fin 4 → Fin k) → ℝ) :
      (∑ p, f p) = ∑ a, ∑ b, ∑ c, ∑ d, f ![a,b,c,d] := by
    let e : (Fin 4 → Fin k) ≃ Fin k × Fin k × Fin k × Fin k :=
      { toFun := fun p => (p 0, p 1, p 2, p 3)
        invFun := fun x => ![x.1, x.2.1, x.2.2.1, x.2.2.2]
        left_inv := by intro p; funext i; fin_cases i <;> rfl
        right_inv := by intro ⟨a,b,c,d⟩; rfl }
    rw [Fintype.sum_equiv e f (fun x => f ![x.1,x.2.1,x.2.2.1,x.2.2.2]) (by
      intro p
      have hp : p = ![p 0,p 1,p 2,p 3] := by funext i; fin_cases i <;> rfl
      simpa [e] using congrArg f hp)]
    simp only [Fintype.sum_prod_type]
  have hconst :
      (∑ a : Fin k, ∑ b : Fin k, ∑ c : Fin k, ∑ d : Fin k,
        if a=b ∧ a=c ∧ a=d then m₄ else 0) = (k : ℝ) * m₄ := by
    simp_rw [ite_and]
    simp
  have hneq (t : ℝ) :
      (∑ a : Fin k, ∑ b : Fin k, if a=b then 0 else t) =
        (k : ℝ) * ((k : ℝ) - 1) * t := by
    have h (a b : Fin k) :
        (if a=b then (0:ℝ) else t) = t - (if a=b then t else 0) := by
      split_ifs <;> ring
    simp_rw [h, Finset.sum_sub_distrib]
    simp
    ring
  have hpair₁ :
      (∑ a : Fin k, ∑ b : Fin k, ∑ c : Fin k, ∑ d : Fin k,
        if a=b ∧ c=d ∧ a≠c then m₂^2 else 0) =
        (k : ℝ) * ((k : ℝ) - 1) * m₂^2 := by
    simp_rw [ite_and]
    simp only [ne_eq, ite_not, Finset.sum_ite_irrel, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte, Finset.sum_const_zero]
    exact hneq (m₂^2)
  have hpair₂ :
      (∑ a : Fin k, ∑ b : Fin k, ∑ c : Fin k, ∑ d : Fin k,
        if a=c ∧ b=d ∧ a≠b then m₂^2 else 0) =
        (k : ℝ) * ((k : ℝ) - 1) * m₂^2 := by
    simp_rw [ite_and]
    simp only [ne_eq, ite_not, Finset.sum_ite_irrel, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte, Finset.sum_const_zero]
    exact hneq (m₂^2)
  have hpair₃ :
      (∑ a : Fin k, ∑ b : Fin k, ∑ c : Fin k, ∑ d : Fin k,
        if a=d ∧ b=c ∧ a≠b then m₂^2 else 0) =
        (k : ℝ) * ((k : ℝ) - 1) * m₂^2 := by
    simp_rw [ite_and]
    simp only [ne_eq, ite_not, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    exact hneq (m₂^2)
  rw [hquad]
  simp_rw [hpoint]
  simp_rw [Finset.sum_add_distrib]
  rw [hconst, hpair₁, hpair₂, hpair₃]
  ring

namespace RowModel

variable {Y : Type*} [Fintype Y] (M : RowModel Y)

/-- A four-score coordinate product has zero expectation when one of its indices occurs
exactly once, because that coordinate has mean zero. -/
theorem expect_four_product_singleton_zero (n : ℕ)
    (p : Fin 4 → Fin (M.N n)) (hp : fourthHasSingleton p) :
    M.expect n (fun ys => ∏ a : Fin 4, M.f n (ys (p a))) = 0 := by
  -- Factor the product by distinct coordinates using `expect_prod_coordinate`.
  -- The factor at the singleton index is `M.centered n`.
  classical
  obtain ⟨i, hi⟩ := hp
  let g : Fin (M.N n) → Y → ℝ := fun j y =>
    ∏ a ∈ Finset.univ.filter (fun a : Fin 4 => p a = j), M.f n y
  have hfactor (ys : Fin (M.N n) → Y) :
      (∏ j, g j (ys j)) = ∏ a : Fin 4, M.f n (ys (p a)) := by
    simp only [g]
    calc
      (∏ j, ∏ a ∈ Finset.univ.filter (fun a : Fin 4 => p a = j), M.f n (ys j)) =
          ∏ j, ∏ a ∈ Finset.univ.filter (fun a : Fin 4 => p a = j),
            M.f n (ys (p a)) := by
            apply Finset.prod_congr rfl
            intro j _
            apply Finset.prod_congr rfl
            intro a ha
            rw [(Finset.mem_filter.mp ha).2]
      _ = ∏ a : Fin 4, M.f n (ys (p a)) := by
        simpa using (Finset.prod_fiberwise Finset.univ p
          (fun a : Fin 4 => M.f n (ys (p a))))
  have hsingle : ∑ y, M.w n y * g i y = 0 := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hi
    simp [g, ha, M.centered n]
  calc
    M.expect n (fun ys => ∏ a : Fin 4, M.f n (ys (p a))) =
        M.expect n (fun ys => ∏ j, g j (ys j)) := by
          congr 1; funext ys; exact (hfactor ys).symm
    _ = ∏ j, ∑ y, M.w n y * g j y := M.expect_prod_coordinate n g
    _ = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hsingle

/-- A four-score product with all four indices equal has expectation equal to the
one-coordinate fourth moment. -/
theorem expect_four_product_constant (n : ℕ)
    (p : Fin 4 → Fin (M.N n)) (hp : fourthConstant p) :
    M.expect n (fun ys => ∏ a : Fin 4, M.f n (ys (p a))) = M.oneFourth n := by
  -- Rewrite the product as `(f n (ys (p 0))) ^ 4` and use `expect_coordinate`.
  have hprod (ys : Fin (M.N n) → Y) :
      (∏ a : Fin 4, M.f n (ys (p a))) = (M.f n (ys (p 0))) ^ 4 := by
    rw [Fin.prod_univ_four]
    simp only [hp 1, hp 2, hp 3]
    ring
  calc
    M.expect n (fun ys => ∏ a : Fin 4, M.f n (ys (p a))) =
        M.expect n (fun ys => (M.f n (ys (p 0))) ^ 4) := by
          congr 1; funext ys; exact hprod ys
    _ = M.oneFourth n := by
      rw [M.expect_coordinate n (p 0) (fun y => (M.f n y) ^ 4)]
      rfl

/-- A four-score product with no singleton and at least two distinct indices has
expectation equal to the square of the one-coordinate second moment. -/
theorem expect_four_product_two_pairs (n : ℕ)
    (p : Fin 4 → Fin (M.N n)) (hs : ¬ fourthHasSingleton p)
    (hc : ¬ fourthConstant p) :
    M.expect n (fun ys => ∏ a : Fin 4, M.f n (ys (p a))) =
      (M.oneSecond n) ^ 2 := by
  -- Four occurrences with no singleton and at least two indices are two pairs.
  -- Rewrite as `f i ^ 2 * f j ^ 2` and use `expect_coordinate_mul`.
  classical
  have hcases :
      (p 0 = p 1 ∧ p 2 = p 3 ∧ p 0 ≠ p 2) ∨
      (p 0 = p 2 ∧ p 1 = p 3 ∧ p 0 ≠ p 1) ∨
      (p 0 = p 3 ∧ p 1 = p 2 ∧ p 0 ≠ p 1) := by
    have hseq : fourthHasSingleton p ↔
        (p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3) ∨
        (p 1 ≠ p 0 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3) ∨
        (p 2 ≠ p 0 ∧ p 2 ≠ p 1 ∧ p 2 ≠ p 3) ∨
        (p 3 ≠ p 0 ∧ p 3 ≠ p 1 ∧ p 3 ≠ p 2) := by
      simp only [fourthHasSingleton, Finset.card_filter, Fin.sum_univ_four]
      constructor
      · rintro ⟨i, hi⟩
        by_cases h0 : p 0 = i <;> by_cases h1 : p 1 = i <;>
          by_cases h2 : p 2 = i <;> by_cases h3 : p 3 = i <;>
          simp_all [eq_comm]
      · rintro (h | h | h | h)
        · refine ⟨p 0, ?_⟩; simp_all [eq_comm]
        · refine ⟨p 1, ?_⟩; simp_all [eq_comm]
        · refine ⟨p 2, ?_⟩; simp_all [eq_comm]
        · refine ⟨p 3, ?_⟩; simp_all [eq_comm]
    have hceq : fourthConstant p ↔ p 0 = p 1 ∧ p 0 = p 2 ∧ p 0 = p 3 := by
      simp [fourthConstant, Fin.forall_fin_succ]
      constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1.symm, h2.symm, h3.symm⟩
    rw [hseq] at hs
    rw [hceq] at hc
    by_cases h01 : p 0 = p 1 <;> by_cases h02 : p 0 = p 2 <;>
      by_cases h03 : p 0 = p 3 <;> by_cases h12 : p 1 = p 2 <;>
      by_cases h13 : p 1 = p 3 <;> by_cases h23 : p 2 = p 3 <;>
      simp_all [eq_comm]
  rcases hcases with ⟨h01, h23, h02⟩ | ⟨h02, h13, h01⟩ | ⟨h03, h12, h01⟩
  · have hprod (ys : Fin (M.N n) → Y) :
        (∏ a : Fin 4, M.f n (ys (p a))) =
          (M.f n (ys (p 0))) ^ 2 * (M.f n (ys (p 2))) ^ 2 := by
      rw [Fin.prod_univ_four, h01, h23]
      ring
    calc
      M.expect n (fun ys => ∏ a : Fin 4, M.f n (ys (p a))) =
          M.expect n (fun ys => (M.f n (ys (p 0))) ^ 2 *
            (M.f n (ys (p 2))) ^ 2) := by
              congr 1; funext ys; exact hprod ys
      _ = (M.oneSecond n) ^ 2 := by
        rw [M.expect_coordinate_mul n (p 0) (p 2) h02
          (fun y => (M.f n y) ^ 2) (fun y => (M.f n y) ^ 2)]
        simp only [oneSecond]
        ring
  · have hprod (ys : Fin (M.N n) → Y) :
        (∏ a : Fin 4, M.f n (ys (p a))) =
          (M.f n (ys (p 0))) ^ 2 * (M.f n (ys (p 1))) ^ 2 := by
      rw [Fin.prod_univ_four, h02, h13]
      ring
    calc
      M.expect n (fun ys => ∏ a : Fin 4, M.f n (ys (p a))) =
          M.expect n (fun ys => (M.f n (ys (p 0))) ^ 2 *
            (M.f n (ys (p 1))) ^ 2) := by
              congr 1; funext ys; exact hprod ys
      _ = (M.oneSecond n) ^ 2 := by
        rw [M.expect_coordinate_mul n (p 0) (p 1) h01
          (fun y => (M.f n y) ^ 2) (fun y => (M.f n y) ^ 2)]
        simp only [oneSecond]
        ring
  · have hprod (ys : Fin (M.N n) → Y) :
        (∏ a : Fin 4, M.f n (ys (p a))) =
          (M.f n (ys (p 0))) ^ 2 * (M.f n (ys (p 1))) ^ 2 := by
      rw [Fin.prod_univ_four, h03, h12]
      ring
    calc
      M.expect n (fun ys => ∏ a : Fin 4, M.f n (ys (p a))) =
          M.expect n (fun ys => (M.f n (ys (p 0))) ^ 2 *
            (M.f n (ys (p 1))) ^ 2) := by
              congr 1; funext ys; exact hprod ys
      _ = (M.oneSecond n) ^ 2 := by
        rw [M.expect_coordinate_mul n (p 0) (p 1) h01
          (fun y => (M.f n y) ^ 2) (fun y => (M.f n y) ^ 2)]
        simp only [oneSecond]
        ring

end RowModel

open Filter

namespace RowModel

variable {Y : Type*} [Fintype Y] (M : RowModel Y)

/-- For a centered finite iid row, the fourth moment of the unnormalized score sum is the
number of coordinates times the one-coordinate fourth moment, plus three times the number
of ordered distinct pairs times the square of the one-coordinate second moment. -/
theorem scoreSum_fourth_expansion (n : ℕ) :
    M.expect n (fun ys => (M.scoreSum n ys) ^ 4) =
      (M.N n : ℝ) * M.oneFourth n +
        3 * (M.N n : ℝ) * ((M.N n : ℝ) - 1) * (M.oneSecond n) ^ 2 := by
  classical
  have hpoint (p : Fin 4 → Fin (M.N n)) :
      M.expect n (fun ys => ∏ a : Fin 4, M.f n (ys (p a))) =
        if fourthHasSingleton p then 0 else
          if fourthConstant p then M.oneFourth n else (M.oneSecond n) ^ 2 := by
    by_cases hs : fourthHasSingleton p
    · simp [hs, M.expect_four_product_singleton_zero n p hs]
    · by_cases hc : fourthConstant p
      · simp [hs, hc, M.expect_four_product_constant n p hc]
      · simp [hs, hc, M.expect_four_product_two_pairs n p hs hc]
  calc
    M.expect n (fun ys => (M.scoreSum n ys) ^ 4) =
        M.expect n (fun ys => ∑ p : Fin 4 → Fin (M.N n),
          ∏ a : Fin 4, M.f n (ys (p a))) := by
            congr 1
            funext ys
            exact Fintype.sum_pow (fun i : Fin (M.N n) => M.f n (ys i)) 4
    _ = ∑ p : Fin 4 → Fin (M.N n),
          M.expect n (fun ys => ∏ a : Fin 4, M.f n (ys (p a))) := by
            simp only [expect, Finset.mul_sum]
            rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [hpoint]
      exact fourth_index_sum (M.N n) (M.oneSecond n) (M.oneFourth n)

/-- [At each row index](hyp:n), [the fourth moment of the square-root-normalized score sum
is bounded by four times the fourth power of the common absolute score bound](goal). -/
theorem normalizedSum_fourth_le (n : ℕ) :
    M.expect n (fun ys => (M.normalizedSum n ys) ^ 4) ≤ 4 * M.B ^ 4 := by
  classical
  have hY : (Finset.univ : Finset Y).Nonempty := by
    by_contra h
    have hm := M.mass_one n
    simp [Finset.not_nonempty_iff_eq_empty.mp h] at hm
  obtain ⟨y₀, _⟩ := hY
  have hB : 0 ≤ M.B := (abs_nonneg _).trans (M.bound n y₀)
  have hfour : M.oneFourth n ≤ M.B ^ 4 := by
    unfold oneFourth
    calc
      (∑ y, M.w n y * (M.f n y) ^ 4) ≤
          ∑ y, M.w n y * M.B ^ 4 := by
            apply Finset.sum_le_sum
            intro y _
            apply mul_le_mul_of_nonneg_left _ (M.mass_nonneg n y)
            have hf2 : (M.f n y) ^ 2 ≤ M.B ^ 2 := by
              have hp : 0 ≤ (M.B - |M.f n y|) * (M.B + |M.f n y|) :=
                mul_nonneg (sub_nonneg.mpr (M.bound n y))
                  (add_nonneg hB (abs_nonneg _))
              nlinarith [sq_abs (M.f n y)]
            calc
              (M.f n y) ^ 4 = ((M.f n y) ^ 2) ^ 2 := by ring
              _ ≤ (M.B ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hf2 2
              _ = M.B ^ 4 := by ring
      _ = M.B ^ 4 := by rw [← Finset.sum_mul, M.mass_one n]; ring
  have hsecond_nonneg : 0 ≤ M.oneSecond n := by
    unfold oneSecond
    apply Finset.sum_nonneg
    intro y _
    exact mul_nonneg (M.mass_nonneg n y) (sq_nonneg _)
  have hsecond : M.oneSecond n ≤ M.B ^ 2 := by
    unfold oneSecond
    calc
      (∑ y, M.w n y * (M.f n y) ^ 2) ≤
          ∑ y, M.w n y * M.B ^ 2 := by
            apply Finset.sum_le_sum
            intro y _
            apply mul_le_mul_of_nonneg_left _ (M.mass_nonneg n y)
            have hp : 0 ≤ (M.B - |M.f n y|) * (M.B + |M.f n y|) :=
              mul_nonneg (sub_nonneg.mpr (M.bound n y))
                (add_nonneg hB (abs_nonneg _))
            nlinarith [sq_abs (M.f n y)]
      _ = M.B ^ 2 := by rw [← Finset.sum_mul, M.mass_one n]; ring
  by_cases hz : M.N n = 0
  · have hzero : M.expect n (fun ys => (M.normalizedSum n ys) ^ 4) = 0 := by
      simp [normalizedSum, scoreSum, hz, expect]
    rw [hzero]
    positivity
  · have hk : 1 ≤ (M.N n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    have hk0 : 0 < (M.N n : ℝ) := by linarith
    have hsqrt : (Real.sqrt (M.N n : ℝ)) ^ 2 = (M.N n : ℝ) :=
      Real.sq_sqrt (by positivity)
    have hscale : ((Real.sqrt (M.N n : ℝ))⁻¹) ^ 4 =
        ((M.N n : ℝ)⁻¹) ^ 2 := by
      calc
        ((Real.sqrt (M.N n : ℝ))⁻¹) ^ 4 =
            (((Real.sqrt (M.N n : ℝ)) ^ 2)⁻¹) ^ 2 := by ring
        _ = _ := by rw [hsqrt]
    have hsecond_sq : (M.oneSecond n) ^ 2 ≤ M.B ^ 4 := by
      have hb2 : 0 ≤ M.B ^ 2 := sq_nonneg _
      nlinarith [mul_nonneg hsecond_nonneg (sub_nonneg.mpr hsecond),
        mul_nonneg hb2 (sub_nonneg.mpr hsecond)]
    have hexp :
        (M.N n : ℝ) * M.oneFourth n +
          3 * (M.N n : ℝ) * ((M.N n : ℝ) - 1) * (M.oneSecond n) ^ 2 ≤
          4 * (M.N n : ℝ) ^ 2 * M.B ^ 4 := by
      have hk1 : 0 ≤ (M.N n : ℝ) - 1 := by linarith
      have hfour0 : 0 ≤ M.B ^ 4 := by positivity
      have hfirst := mul_le_mul_of_nonneg_left hfour (le_of_lt hk0)
      have hpair := mul_le_mul_of_nonneg_left hsecond_sq
        (show 0 ≤ 3 * (M.N n : ℝ) * ((M.N n : ℝ) - 1) by positivity)
      have hkk : (M.N n : ℝ) ≤ (M.N n : ℝ) ^ 2 := by nlinarith [mul_nonneg hk0.le hk1]
      have hlast := mul_le_mul_of_nonneg_right hkk hfour0
      have hgap : 0 ≤ (M.N n : ℝ) * M.B ^ 4 := mul_nonneg hk0.le hfour0
      nlinarith [mul_nonneg hk0.le hfour0, mul_nonneg hk1 hfour0]
    calc
      M.expect n (fun ys => (M.normalizedSum n ys) ^ 4) =
          ((M.N n : ℝ)⁻¹) ^ 2 *
            ((M.N n : ℝ) * M.oneFourth n +
              3 * (M.N n : ℝ) * ((M.N n : ℝ) - 1) * (M.oneSecond n) ^ 2) := by
            calc
              M.expect n (fun ys => (M.normalizedSum n ys) ^ 4) =
                  ((M.N n : ℝ)⁻¹) ^ 2 *
                    M.expect n (fun ys => (M.scoreSum n ys) ^ 4) := by
                      simp only [normalizedSum, mul_pow, hscale, expect,
                        Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro ys _
                      ring
              _ = _ := by rw [M.scoreSum_fourth_expansion]
      _ ≤ ((M.N n : ℝ)⁻¹) ^ 2 * (4 * (M.N n : ℝ) ^ 2 * M.B ^ 4) := by
        exact mul_le_mul_of_nonneg_left hexp (sq_nonneg _)
      _ = 4 * M.B ^ 4 := by field_simp

end RowModel
end Causalean.Stat.CLT.FiniteIidTriangular
