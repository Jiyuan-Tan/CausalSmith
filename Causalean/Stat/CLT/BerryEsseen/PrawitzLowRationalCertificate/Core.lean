module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCompactRationalData

/-! # Low Prawitz certificate: unreduced-fraction arithmetic and checker

Unreduced integer-fraction arithmetic, the rounded low-cell integers, and
the Boolean prefix checker with its soundness lemma. The data tables and
the kernel-checked blocks that consume them live in sibling modules.
-/

@[expose] public section

namespace Causalean.Stat.CLT.BerryEsseen

/-- The rational value of an unreduced integer pair (numerator, denominator)
is the numerator divided by the denominator; a zero denominator gives zero. -/
def lowRawVal (q : ℤ × ℤ) : ℚ := (q.1 : ℚ) / (q.2 : ℚ)

/-- The pair (numerator, denominator) of a rational number in lowest terms. -/
def lowRawRat (x : ℚ) : ℤ × ℤ := (x.num, x.den)

/-- Multiplication of unreduced fractions: numerators and denominators are
multiplied separately, with no reduction to lowest terms. -/
def lowRawMul (q r : ℤ × ℤ) : ℤ × ℤ := (q.1 * r.1, q.2 * r.2)

/-- Division of unreduced fractions: (n₁, d₁) divided by (n₂, d₂) is
(n₁·d₂, d₁·n₂), with no reduction to lowest terms. -/
def lowRawDiv (q r : ℤ × ℤ) : ℤ × ℤ := (q.1 * r.2, q.2 * r.1)

/-- Addition of unreduced fractions by cross-multiplication,
(n₁·d₂ + n₂·d₁, d₁·d₂), except that when one summand has zero denominator
(rational value zero) the other summand is returned unchanged. -/
def lowRawAdd (q r : ℤ × ℤ) : ℤ × ℤ :=
  if q.2 = 0 then r else if r.2 = 0 then q
  else (q.1 * r.2 + r.1 * q.2, q.2 * r.2)

/-- The ceiling of the integer fraction with numerator n and denominator d,
computed by integer division:
−⌊−n/d⌋ when d ≥ 0 and −⌊n/(−d)⌋ when d < 0. A zero denominator gives zero. -/
def lowRawCeil (q : ℤ × ℤ) : ℤ :=
  if 0 ≤ q.2 then -(-q.1 / q.2) else -(q.1 / -q.2)

private theorem lowRawRat_val (x : ℚ) : lowRawVal (lowRawRat x) = x := by
  exact Rat.num_div_den x

private theorem lowRawMul_val (q r : ℤ × ℤ) :
    lowRawVal (lowRawMul q r) = lowRawVal q * lowRawVal r := by
  simp only [lowRawVal, lowRawMul, Int.cast_mul, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem lowRawDiv_val (q r : ℤ × ℤ) :
    lowRawVal (lowRawDiv q r) = lowRawVal q / lowRawVal r := by
  simp only [lowRawVal, lowRawDiv, Int.cast_mul, div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

private theorem lowRawAdd_val (q r : ℤ × ℤ) :
    lowRawVal (lowRawAdd q r) = lowRawVal q + lowRawVal r := by
  by_cases hq : q.2 = 0
  · simp [lowRawAdd, lowRawVal, hq]
  by_cases hr : r.2 = 0
  · simp [lowRawAdd, lowRawVal, hq, hr]
  simp only [lowRawAdd, hq, hr, if_false, lowRawVal, Int.cast_add, Int.cast_mul]
  have hq' : (q.2 : ℚ) ≠ 0 := by exact_mod_cast hq
  have hr' : (r.2 : ℚ) ≠ 0 := by exact_mod_cast hr
  field_simp

private theorem lowRawCeil_val (q : ℤ × ℤ) :
    lowRawCeil q = ⌈lowRawVal q⌉ := by
  rcases q with ⟨n, d⟩
  by_cases hd : 0 ≤ d
  · have ht := Int.toNat_of_nonneg hd
    have hc : (d.toNat : ℚ) = (d : ℚ) := by exact_mod_cast ht
    simpa only [lowRawCeil, lowRawVal, if_pos hd, ht, hc] using
      (Rat.ceil_intCast_div_natCast n d.toNat).symm
  · have ht := Int.toNat_of_nonneg (show 0 ≤ -d by omega)
    have hc : ((-d).toNat : ℚ) = (-d : ℤ) := by exact_mod_cast ht
    simpa only [lowRawCeil, lowRawVal, if_neg hd, ht, hc, Int.cast_neg,
      neg_neg, neg_div_neg_eq] using
      (Rat.ceil_intCast_div_natCast (-n) (-d).toNat).symm

/-- The integer Taylor numerator at integers n and d is the sum over k from 0
to 15 of (15!/k!)·nᵏ·d^(15−k), written in Horner form. For d ≠ 0 it equals
15!·d¹⁵ times the sixteen-term Taylor polynomial of the exponential at
n/d. -/
def lowTaylorNum (n d : ℤ) : ℤ :=
  (1307674368000 * d ^ 15 + n *
    (1307674368000 * d ^ 14 + n *
    (653837184000 * d ^ 13 + n *
    (217945728000 * d ^ 12 + n *
    (54486432000 * d ^ 11 + n *
    (10897286400 * d ^ 10 + n *
    (1816214400 * d ^ 9 + n *
    (259459200 * d ^ 8 + n *
    (32432400 * d ^ 7 + n *
    (3603600 * d ^ 6 + n *
    (360360 * d ^ 5 + n *
    (32760 * d ^ 4 + n *
    (2730 * d ^ 3 + n *
    (210 * d ^ 2 + n *
    (15 * d ^ 1 + n *
    1)))))))))))))))

/-- Exact polynomial evaluation on a nonzero integer denominator. -/
private theorem lowTaylor_fraction (n d : ℤ) (hd : d ≠ 0) :
    prawitzTaylor16 ((n : ℚ) / (d : ℚ)) =
      (lowTaylorNum n d : ℚ) / ((1307674368000 * d ^ 15 : ℤ) : ℚ) := by
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  unfold lowTaylorNum
  push_cast
  norm_num [prawitzTaylor16, Finset.sum_range_succ, Nat.factorial]
  field_simp
  ring

/-- The sixteen-term Taylor polynomial of the exponential evaluated on an
unreduced fraction (n, d), returned as the unreduced fraction whose numerator
is the integer Taylor numerator at (n, d) and whose denominator is 15!·d¹⁵.
For d = 0 (rational value zero) it returns (1, 1). -/
def lowRawTaylor (q : ℤ × ℤ) : ℤ × ℤ :=
  if q.2 = 0 then (1, 1)
  else (lowTaylorNum q.1 q.2, 1307674368000 * q.2 ^ 15)

private theorem lowRawTaylor_val (q : ℤ × ℤ) :
    lowRawVal (lowRawTaylor q) = prawitzTaylor16 (lowRawVal q) := by
  by_cases hd : q.2 = 0
  · norm_num [lowRawTaylor, lowRawVal, hd, prawitzTaylor16, Finset.sum_range_succ]
  · simpa only [lowRawTaylor, if_neg hd, lowRawVal] using
      (lowTaylor_fraction q.1 q.2 hd).symm

/-- The n-th power of an unreduced fraction: numerator and denominator are
raised to the power separately. -/
def lowRawPow (q : ℤ × ℤ) (n : ℕ) : ℤ × ℤ := (q.1 ^ n, q.2 ^ n)

private theorem lowRawPow_val (q : ℤ × ℤ) (n : ℕ) :
    lowRawVal (lowRawPow q n) = lowRawVal q ^ n := by
  simp [lowRawPow, lowRawVal, div_pow]

/-- Of two unreduced fractions, the one with the smaller rational value (the
first when they tie), returned in its given unreduced representation. -/
def lowRawMin (q r : ℤ × ℤ) : ℤ × ℤ :=
  if 0 < q.2 ∧ 0 < r.2 then
    if q.1 * r.2 ≤ r.1 * q.2 then q else r
  else if lowRawVal q ≤ lowRawVal r then q else r

private theorem lowRawMin_val (q r : ℤ × ℤ) :
    lowRawVal (lowRawMin q r) = min (lowRawVal q) (lowRawVal r) := by
  unfold lowRawMin
  by_cases hp : 0 < q.2 ∧ 0 < r.2
  · rw [if_pos hp]
    have hq : (0 : ℚ) < q.2 := by exact_mod_cast hp.1
    have hr : (0 : ℚ) < r.2 := by exact_mod_cast hp.2
    have he : lowRawVal q ≤ lowRawVal r ↔ q.1 * r.2 ≤ r.1 * q.2 := by
      unfold lowRawVal
      rw [div_le_div_iff₀ hq hr]
      norm_cast
    split_ifs with h
    · exact (min_eq_left (he.mpr h)).symm
    · exact (min_eq_right (le_of_not_ge (fun hn => h (he.mp hn)))).symm
  · rw [if_neg hp]
    split_ifs with h
    · exact (min_eq_left h).symm
    · exact (min_eq_right (le_of_not_ge h)).symm

private theorem lowCeil_mul_min (c a b : ℚ) (hc : 0 ≤ c) :
    ⌈c * min a b⌉ = min ⌈c * a⌉ ⌈c * b⌉ := by
  rcases le_total a b with h | h
  · have hm := mul_le_mul_of_nonneg_left h hc
    simp [min_eq_left h, min_eq_left (Int.ceil_mono hm)]
  · have hm := mul_le_mul_of_nonneg_left h hc
    simp [min_eq_right h, min_eq_right (Int.ceil_mono hm)]

/-- The two branches of the rational low cell bound for parameter cell j and
frequency index i, each multiplied by one hundred million and kept as an
unreduced integer fraction: first the Taylor branch, second the modulus-sum
branch. Neither is rounded here. -/
def lowCellBranches (j i : ℕ) : (ℤ × ℤ) × (ℤ × ℤ) :=
  let r := lowRawRat (prawitzCompactLeft j)
  let s := lowRawRat (prawitzCompactRight j)
  let a : ℤ × ℤ := (i, 200)
  let b : ℤ × ℤ := (i + 1, 200)
  let neg : ℤ × ℤ := (-1, 1)
  let e := lowRawMin
    (lowRawAdd (lowRawDiv (lowRawPow a 2) (2, 1))
      (lowRawMul neg (lowRawDiv (lowRawMul s (lowRawPow a 3)) (5, 1))))
    (lowRawAdd (lowRawDiv (lowRawPow b 2) (2, 1))
      (lowRawMul neg (lowRawDiv (lowRawMul s (lowRawPow b 3)) (5, 1))))
  let c := lowRawMul (100000000, 200) (lowRawAdd
    (lowRawDiv (1, 1) (lowRawMul (314159, 100000) a))
    (lowRawDiv (lowRawMul (5, 1) s) (12, 1)))
  (lowRawMul c (lowRawDiv
      (lowRawAdd (lowRawDiv (lowRawPow b 3) (6, 1))
        (lowRawDiv (lowRawMul s (lowRawPow b 4)) (8, 1)))
      (lowRawTaylor (lowRawDiv e (2, 1)))),
    lowRawMul c (lowRawDiv
      (lowRawAdd (lowRawDiv (1, 1) (lowRawTaylor e))
        (lowRawDiv (1, 1) (lowRawTaylor (lowRawDiv (lowRawPow a 2) (2, 1))))) r))

/-- The integer low-frequency cell for parameter cell j and frequency index i
is the smaller of the ceilings of the two branch fractions. It equals the
rational low cell bound multiplied by one hundred million and rounded up. -/
def lowCellInteger (j i : ℕ) : ℤ :=
  min (lowRawCeil (lowCellBranches j i).1) (lowRawCeil (lowCellBranches j i).2)

private theorem lowCellInteger_eq (j i : ℕ) :
    lowCellInteger j i = ⌈100000000 * prawitzRationalLowCell j i⌉ := by
  have hs : 0 ≤ prawitzCompactRight j := by
    unfold prawitzCompactRight prawitzCompactLeft
    split_ifs <;> positivity
  unfold lowCellInteger lowCellBranches prawitzRationalLowCell
  dsimp only
  rw [lowRawCeil_val, lowRawCeil_val]
  simp only [lowRawMul_val, lowRawDiv_val, lowRawAdd_val, lowRawPow_val,
    lowRawMin_val, lowRawRat_val, lowRawTaylor_val]
  norm_num only [lowRawVal, Int.cast_ofNat, Int.cast_neg, Int.cast_one,
    Int.cast_add, Int.cast_natCast, Nat.cast_add, Nat.cast_one, neg_mul,
    one_mul, div_one, neg_one_mul, sub_eq_add_neg]
  rw [← lowCeil_mul_min _ _ _ (by positivity)]
  congr 1
  ring_nf

/-- The integer prefix sum for parameter cell j and length n is the sum of the
integer low-frequency cells over frequency indices 1 through n; it is zero
for n = 0. -/
def lowIntPrefix (j : ℕ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => lowIntPrefix j n + lowCellInteger j (n + 1)

private theorem lowIntPrefix_sum (j n : ℕ) :
    lowIntPrefix j n = ∑ i ∈ Finset.Ico 1 (n + 1), lowCellInteger j i := by
  induction n with
  | zero => simp [lowIntPrefix]
  | succ n ih =>
    rw [lowIntPrefix, Finset.sum_Ico_succ_top (by omega), ih]

private theorem lowIntPrefix_cutoff (j k : ℕ) :
    lowIntPrefix j (k - 1) = ∑ i ∈ Finset.Ico 1 k, lowCellInteger j i := by
  cases k with
  | zero => simp [lowIntPrefix]
  | succ k => simpa using lowIntPrefix_sum j k

set_option maxRecDepth 1000000

/-- The Boolean test that an unreduced fraction (n, d) is at most an integer
z, decided in integer arithmetic: it holds exactly when d > 0 and n ≤ z·d.
When it holds, the ceiling of the fraction is at most z. -/
def lowBranchBound (q : ℤ × ℤ) (z : ℤ) : Bool :=
  decide (0 < q.2 ∧ q.1 ≤ z * q.2)

private theorem lowBranchBound_sound (q : ℤ × ℤ) (z : ℤ)
    (h : lowBranchBound q z = true) : lowRawCeil q ≤ z := by
  have hq : 0 < q.2 ∧ q.1 ≤ z * q.2 := by simpa [lowBranchBound] using h
  rw [lowRawCeil_val, Int.ceil_le]
  unfold lowRawVal
  apply (div_le_iff₀ (show (0 : ℚ) < q.2 by exact_mod_cast hq.1)).2
  exact_mod_cast hq.2

/-- The Boolean test that the integer low-frequency cell at (j, i) is at most
an integer z: it holds when at least one of the two branch fractions passes
the fraction test against z, which suffices because the cell is the smaller
of the two rounded branches. -/
def lowCellBound (j i : ℕ) (z : ℤ) : Bool :=
  lowBranchBound (lowCellBranches j i).1 z ||
    lowBranchBound (lowCellBranches j i).2 z

private theorem lowCellBound_sound (j i : ℕ) (z : ℤ)
    (h : lowCellBound j i z = true) : lowCellInteger j i ≤ z := by
  have hb : lowBranchBound (lowCellBranches j i).1 z = true ∨
      lowBranchBound (lowCellBranches j i).2 z = true := by
    simpa only [lowCellBound, Bool.or_eq_true] using h
  rcases hb with h | h
  · exact (min_le_left _ _).trans (lowBranchBound_sound _ _ h)
  · exact (min_le_right _ _).trans (lowBranchBound_sound _ _ h)

/-- The Boolean test that a list of integers bounds, entry by entry, the
integer low-frequency cells of parameter cell j at frequency indices n,
n − 1, …, 1 (the list is in decreasing index order): it holds exactly when
the list has length n and every cell passes the cell test against its entry. -/
def lowCheckPrefix (j : ℕ) : ℕ → List ℤ → Bool
  | 0, [] => true
  | n + 1, z :: zs => lowCellBound j (n + 1) z && lowCheckPrefix j n zs
  | _, _ => false

private theorem lowCheckPrefix_sound (j n : ℕ) (zs : List ℤ)
    (h : lowCheckPrefix j n zs = true) : lowIntPrefix j n ≤ zs.sum := by
  induction n generalizing zs with
  | zero =>
    cases zs with
    | nil => simp [lowIntPrefix]
    | cons z zs => simp [lowCheckPrefix] at h
  | succ n ih =>
    cases zs with
    | nil => simp [lowCheckPrefix] at h
    | cons z zs =>
      have hb : lowCellBound j (n + 1) z = true ∧ lowCheckPrefix j n zs = true := by
        simpa only [lowCheckPrefix, Bool.and_eq_true] using h
      simpa only [lowIntPrefix, List.sum_cons, add_comm] using
        add_le_add (ih zs hb.2) (lowCellBound_sound j (n + 1) z hb.1)

/-- Checked prefix bounds plus the original rounded initial cell bound the total. -/
private theorem lowInteger_of_certificate (j : ℕ) (zs : List ℤ)
    (hc : lowCheckPrefix j (prawitzLowCutoffIndex j - 1) zs = true)
    (ht : (⌈100000000 * prawitzRationalLowInitial j⌉ + zs.sum : ℤ) ≤ 25000000) :
    (⌈100000000 * prawitzRationalLowInitial j⌉ +
      lowIntPrefix j (prawitzLowCutoffIndex j - 1) : ℤ) ≤ 25000000 :=
  (add_le_add le_rfl (lowCheckPrefix_sound j _ zs hc)).trans ht

end Causalean.Stat.CLT.BerryEsseen
