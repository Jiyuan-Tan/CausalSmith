module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.DerivativeChains
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.DerivativeCoefficients
/-!
# Weighted increasing-chain bounds for differentiation

Prefix-weight telescoping supplies the factorial gain in powers of the
shifted-Legendre differentiation matrix; weighted Cauchy--Schwarz bounds its action.
-/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.RdTruesideNoiseFrontier

/-- Summing prefix powers of the endpoint weights gains one power and its divisor. Given [the displayed inputs and assumptions](hyp:n,r), [the stated mathematical conclusion holds](goal). -/
lemma shiftedLegendre_prefix_power_bound (n r : ℕ) :
    (r+1 : ℝ) * (∑ i ∈ Finset.range n, (2*(i : ℝ)+1) * ((i : ℝ)^2)^r) ≤
      ((n : ℝ)^2)^(r+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add]
    have h := nonnegative_power_linear_terms_le ((n : ℝ)^2) (2*(n : ℝ)+1)
      (sq_nonneg _) (by positivity) r
    have he : (n : ℝ)^2 + (2*(n : ℝ)+1) = ((n+1 : ℕ) : ℝ)^2 := by
      push_cast; ring
    rw [he] at h
    calc
      _ ≤ ((n : ℝ)^2)^(r+1) + (r+1 : ℝ)*((2*(n : ℝ)+1)*((n : ℝ)^2)^r) :=
        add_le_add ih le_rfl
      _ ≤ _ := by simpa only [mul_assoc] using h

/-- The entries of the iterated derivative matrix, multiplied on the right. Given [the displayed inputs and assumptions](hyp:m), [this definition specifies the stated object](goal). -/
def legendreDerivativePower (m : ℕ) : ℕ → ℕ → ℕ → ℝ
  | 0, k, l => if k = l then 1 else 0
  | j+1, k, l => ∑ i ∈ Finset.range (m+1),
      legendreDerivativePower m j k i * legendreDerivativeEntry i l

/-- Matrix entries are nonnegative, so deleting parity restrictions preserves an upper bound. Given [the displayed inputs and assumptions](hyp:m,j,k,l), [the stated mathematical conclusion holds](goal). -/
lemma legendreDerivativePower_nonneg (m j k l : ℕ) :
    0 ≤ legendreDerivativePower m j k l := by
  induction j generalizing k l with
  | zero => simp only [legendreDerivativePower]; split_ifs <;> norm_num
  | succ j ih =>
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg (ih k i)
    unfold legendreDerivativeEntry
    split_ifs <;> first | positivity | exact le_rfl

/-- After positive differentiation order only strictly increasing index paths survive. Given [the displayed inputs and assumptions](hyp:m,j,k,l,hj,hkl), [the stated mathematical conclusion holds](goal). -/
lemma legendreDerivativePower_eq_zero (m j k l : ℕ) (hj : 1 ≤ j) (hkl : l ≤ k) :
    legendreDerivativePower m j k l = 0 := by
  cases j with
  | zero => omega
  | succ j =>
    induction j generalizing k l with
    | zero =>
      simp only [legendreDerivativePower]
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hki : k = i
      · subst i; simp [legendreDerivativeEntry, show ¬ k < l by omega]
      · simp [hki]
    | succ j ih =>
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hil : i < l
      · rw [ih k i (by omega) (by omega)]
        simp
      · simp [legendreDerivativeEntry, hil]

/-- Prefix-weight telescoping bounds all increasing chains, with one factorial per internal index. Given [the displayed inputs and assumptions](hyp:m,j,k,l,hj), [the stated mathematical conclusion holds](goal). -/
lemma legendreDerivativePower_entry_bound (m j k l : ℕ) (hj : 1 ≤ j) :
    legendreDerivativePower m j k l ≤
      2^j * (2*(k : ℝ)+1) * ((l : ℝ)^2)^(j-1) / (Nat.factorial (j-1) : ℝ) := by
  cases j with
  | zero => omega
  | succ j =>
    induction j generalizing k l with
    | zero =>
      simp only [legendreDerivativePower]
      calc
        _ ≤ legendreDerivativeEntry k l := by
          by_cases hk : k ∈ Finset.range (m+1)
          · simp [hk]
          · have hz : (∑ i ∈ Finset.range (m+1),
                (if k = i then (1 : ℝ) else 0) * legendreDerivativeEntry i l) = 0 := by
              apply Finset.sum_eq_zero
              intro i hi
              have hki : k ≠ i := by intro he; subst i; exact hk hi
              simp [hki]
            rw [hz]
            unfold legendreDerivativeEntry
            split_ifs <;> positivity
        _ ≤ _ := by simp [legendreDerivativeEntry]; split_ifs <;> first | positivity | exact le_rfl
    | succ j ih =>
      have hsum : legendreDerivativePower m (j+2) k l ≤
          ∑ i ∈ Finset.range l,
            (2^(j+1) * (2*(k : ℝ)+1) * ((i : ℝ)^2)^j /
              (Nat.factorial j : ℝ)) * (2*(2*(i : ℝ)+1)) := by
        unfold legendreDerivativePower
        calc
          _ ≤ ∑ i ∈ Finset.range (m+1),
              if i < l then
                (2^(j+1) * (2*(k : ℝ)+1) * ((i : ℝ)^2)^j /
                  (Nat.factorial j : ℝ)) * (2*(2*(i : ℝ)+1)) else 0 := by
            apply Finset.sum_le_sum
            intro i hi
            by_cases hil : i < l
            · simp only [hil, if_true]
              apply mul_le_mul (by simpa using ih k i (by omega))
                (by simp [legendreDerivativeEntry]; split_ifs <;> first | positivity | exact le_rfl)
                (by unfold legendreDerivativeEntry; split_ifs <;> first | positivity | exact le_rfl) (by positivity)
            · simp [legendreDerivativeEntry, hil]
          _ ≤ _ := by
            rw [← Finset.sum_filter]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro i hi
              exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
            · intro i hi hn; positivity
      have hp := shiftedLegendre_prefix_power_bound l j
      have hf : (Nat.factorial (j+1) : ℝ) = (j+1 : ℝ)*(Nat.factorial j : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; rfl
      calc
        _ ≤ _ := hsum
        _ = (2^(j+2) * (2*(k : ℝ)+1) / (Nat.factorial j : ℝ)) *
            (∑ i ∈ Finset.range l, (2*(i : ℝ)+1)*((i : ℝ)^2)^j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [pow_succ]
          ring
        _ ≤ 2^(j+2) * (2*(k : ℝ)+1) * ((l : ℝ)^2)^(j+1) /
            (Nat.factorial (j+1) : ℝ) := by
          rw [hf]
          have hp' : (∑ i ∈ Finset.range l, (2*(i : ℝ)+1)*((i : ℝ)^2)^j) ≤
              ((l : ℝ)^2)^(j+1)/(j+1 : ℝ) :=
            (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hp)
          have hh := mul_le_mul_of_nonneg_left hp'
            (show 0 ≤ 2^(j+2) * (2*(k : ℝ)+1) / (Nat.factorial j : ℝ) by positivity)
          calc
            _ ≤ _ := hh
            _ = _ := by
              field_simp
              <;> ring
        _ = _ := by simp only [Nat.add_sub_cancel]

/-- The recursively multiplied entries act on coefficients exactly as repeated differentiation. Given [the displayed inputs and assumptions](hyp:m,j,c,k,hk), [the stated mathematical conclusion holds](goal). -/
lemma legendreDerivativePower_action (m j : ℕ) (c : ℕ → ℝ) (k : ℕ)
    (hk : k ∈ Finset.range (m+1)) :
    ((legendreDerivativeAction m)^[j]) c k =
      ∑ l ∈ Finset.range (m+1), legendreDerivativePower m j k l * c l := by
  induction j generalizing c with
  | zero => simp [legendreDerivativePower, hk]
  | succ j ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [legendreDerivativeAction, Finset.mul_sum, legendreDerivativePower,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro i hi
    ring

/-- Weighted Cauchy--Schwarz transfers a separable entry bound to the weighted coefficient norm. Given [the displayed inputs and assumptions](hyp:s,D,c,w,B,hw,hD), [the stated mathematical conclusion holds](goal). -/
lemma weighted_derivative_matrix_action_bound (s : Finset ℕ)
    (D : ℕ → ℕ → ℝ) (c w : ℕ → ℝ) (B : ℝ)
    (hw : ∀ k ∈ s, 0 < w k)
    (hD : ∀ k ∈ s, ∀ l ∈ s, (D k l)^2 ≤ B^2*(w k)^2) :
    (∑ k ∈ s, (∑ l ∈ s, D k l*c l)^2 / w k) ≤
      B^2*(∑ k ∈ s, w k)^2*(∑ l ∈ s, (c l)^2/w l) := by
  have hE : 0 ≤ ∑ l ∈ s, (c l)^2/w l :=
    Finset.sum_nonneg (fun l hl => div_nonneg (sq_nonneg _) (hw l hl).le)
  calc
    _ ≤ ∑ k ∈ s, B^2*w k*(∑ l ∈ s, w l)*(∑ l ∈ s, (c l)^2/w l) := by
      apply Finset.sum_le_sum
      intro k hk
      have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
        (r := fun l => D k l*c l)
        (f := fun l => (D k l)^2*w l) (g := fun l => (c l)^2/w l)
        (by intro l hl; exact mul_nonneg (sq_nonneg _) (hw l hl).le)
        (by intro l hl; exact div_nonneg (sq_nonneg _) (hw l hl).le)
        (by intro l hl; apply le_of_eq; field_simp [(hw l hl).ne'] <;> ring)
      have hmass : (∑ l ∈ s, (D k l)^2*w l) ≤ B^2*(w k)^2*(∑ l ∈ s, w l) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro l hl
        exact mul_le_mul_of_nonneg_right (hD k hk l hl) (hw l hl).le
      have hpoint := hcs.trans (mul_le_mul_of_nonneg_right hmass hE)
      calc
        _ ≤ (B^2*(w k)^2*(∑ l ∈ s, w l)*(∑ l ∈ s, (c l)^2/w l))/w k :=
          div_le_div_of_nonneg_right hpoint (hw k hk).le
        _ = _ := by field_simp [(hw k hk).ne'] <;> ring
    _ = _ := by
      simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
      ring

/-- Every power of the Legendre differentiation action has the roadmap's factorial norm bound. Given [the displayed inputs and assumptions](hyp:m,j,hj,c), [the stated mathematical conclusion holds](goal). -/
lemma legendreDerivativeAction_factorial_bound (m j : ℕ) (hj : 1 ≤ j) (c : ℕ → ℝ) :
    (∑ k ∈ Finset.range (m+1),
      (((legendreDerivativeAction m)^[j]) c k)^2/(2*(k : ℝ)+1)) ≤
      (4^j*((m : ℝ)+1)^(2*j)/(Nat.factorial j : ℝ))^2 *
        (∑ k ∈ Finset.range (m+1), (c k)^2/(2*(k : ℝ)+1)) := by
  let B : ℝ := 2^j*((m : ℝ)+1)^(2*(j-1))/(Nat.factorial (j-1) : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hentry (k l : ℕ) (hl : l ∈ Finset.range (m+1)) :
      legendreDerivativePower m j k l ≤ B*(2*(k : ℝ)+1) := by
    have hlm : (l : ℝ) ≤ (m : ℝ)+1 := by
      exact_mod_cast Nat.le_of_lt (Finset.mem_range.mp hl)
    have hp : ((l : ℝ)^2)^(j-1) ≤ (((m : ℝ)+1)^2)^(j-1) := by
      gcongr
    calc
      _ ≤ 2^j*(2*(k : ℝ)+1)*((l : ℝ)^2)^(j-1)/(Nat.factorial (j-1) : ℝ) :=
        legendreDerivativePower_entry_bound m j k l hj
      _ ≤ 2^j*(2*(k : ℝ)+1)*(((m : ℝ)+1)^2)^(j-1)/(Nat.factorial (j-1) : ℝ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by dsimp [B]; rw [← pow_mul]; ring
  have hsquare (k : ℕ) (hk : k ∈ Finset.range (m+1))
      (l : ℕ) (hl : l ∈ Finset.range (m+1)) :
      (legendreDerivativePower m j k l)^2 ≤ B^2*(2*(k : ℝ)+1)^2 := by
    have h := mul_self_le_mul_self (legendreDerivativePower_nonneg m j k l) (hentry k l hl)
    simpa only [pow_two, mul_assoc, mul_left_comm, mul_comm] using h
  have hm := weighted_derivative_matrix_action_bound (Finset.range (m+1))
    (legendreDerivativePower m j) c (fun k => 2*(k : ℝ)+1) B
    (by intro k hk; positivity) hsquare
  have hcoeff : (∑ k ∈ Finset.range (m+1),
      (((legendreDerivativeAction m)^[j]) c k)^2/(2*(k : ℝ)+1)) =
      ∑ k ∈ Finset.range (m+1),
        (∑ l ∈ Finset.range (m+1), legendreDerivativePower m j k l*c l)^2/(2*(k : ℝ)+1) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [legendreDerivativePower_action m j c k hk]
  rw [hcoeff]
  rw [shiftedLegendre_total_weight] at hm
  have hfactor : B*((m : ℝ)+1)^2 ≤
      4^j*((m : ℝ)+1)^(2*j)/(Nat.factorial j : ℝ) := by
    have he : 2*(j-1)+2 = 2*j := by omega
    have hf := mul_le_mul_of_nonneg_right (derivative_chain_factorial_gain j hj)
      (show 0 ≤ ((m : ℝ)+1)^(2*j) by positivity)
    calc
      _ = (2^j/(Nat.factorial (j-1) : ℝ))*((m : ℝ)+1)^(2*j) := by
        dsimp [B]
        rw [div_mul_eq_mul_div, mul_assoc, ← pow_add, he]
        ring
      _ ≤ _ := by simpa only [div_mul_eq_mul_div] using hf
  have hfactorSq : B^2*(((m : ℝ)+1)^2)^2 ≤
      (4^j*((m : ℝ)+1)^(2*j)/(Nat.factorial j : ℝ))^2 := by
    have h := mul_self_le_mul_self (mul_nonneg hB (sq_nonneg _)) hfactor
    simpa only [pow_two, mul_assoc, mul_left_comm, mul_comm] using h
  exact hm.trans (mul_le_mul_of_nonneg_right hfactorSq
    (Finset.sum_nonneg (fun k hk => by positivity)))

end CausalSmith.Stat.RdTruesideNoiseFrontier
