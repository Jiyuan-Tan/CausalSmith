module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Powerset
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# One shared latent sign in a finite cell

The latent sign is mixed once after multiplying all record factors. Cells carry
bounded real scores, Boolean assignments, and an optional Boolean thinning of
the positive assignments. Posterior coefficients are defined for arbitrary
subsets; cancellation is stated only for subsets of positive assignments.
-/

@[expose] public section

open scoped BigOperators
noncomputable section
namespace Causalean.Stat.Minimax.Mixture.PoissonLatentSign

/-- A cell of the given size consists of scores, assignments, and selection flags.
The product measurable space allows arbitrary conditional laws of these data. -/
abbrev Cell (m : ℕ) : Type := (Fin m → ℝ) × ((Fin m → Bool) × (Fin m → Bool))

/-- The Boolean latent or assignment sign is interpreted as plus or minus one. -/
def sign (b : Bool) : ℝ := if b then 1 else -1

/-- The active set contains precisely the positively assigned records. -/
def active {m : ℕ} (c : Cell m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => c.2.1 i = true)

/-- The selected set contains precisely the records retained by the selection flags. -/
def selected {m : ℕ} (c : Cell m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => c.2.2 i = true)

/-- Valid cell data have scores bounded by one and selection contained in the active set. -/
def Valid {m : ℕ} (c : Cell m) : Prop :=
  (∀ i, |c.1 i| ≤ 1) ∧ selected c ⊆ active c

/-- The sign likelihood at a latent sign ℓ is the product over all records of 1 + τ · ℓ · uᵢ · sᵢ, where uᵢ is the record's score and sᵢ = ±1 its assignment sign. -/
def signLikelihood {m : ℕ} (τ : ℝ) (c : Cell m) (ell : ℝ) : ℝ :=
  ∏ i, (1 + τ * ell * c.1 i * sign (c.2.1 i))

/-- The posterior denominator is the sum of the likelihoods at the two latent signs. -/
def denominator {m : ℕ} (τ : ℝ) (c : Cell m) : ℝ :=
  signLikelihood τ c 1 + signLikelihood τ c (-1)

/-- The posterior coefficient of a set S of records is the average over the shared sign, weighted by the two sign likelihoods and divided by their sum, of the product over S of uᵢ/(1 + τuᵢ) at sign +1 and of −uᵢ/(1 − τuᵢ) at sign −1, where uᵢ are the scores. -/
def posterior {m : ℕ} (τ : ℝ) (c : Cell m) (S : Finset (Fin m)) : ℝ :=
  (signLikelihood τ c 1 * (∏ i ∈ S, c.1 i / (1 + τ * c.1 i)) +
    signLikelihood τ c (-1) * (∏ i ∈ S, (-c.1 i) / (1 - τ * c.1 i))) /
    denominator τ c

/-- Every record likelihood factor lies between three quarters and five quarters
when the score and sign bounds hold. -/
theorem factor_bounds {τ u ell σ : ℝ} (hτ : |τ| ≤ 1 / 4)
    (hu : |u| ≤ 1) (hell : |ell| = 1) (hσ : |σ| = 1) :
    3 / 4 ≤ 1 + τ * ell * u * σ ∧ 1 + τ * ell * u * σ ≤ 5 / 4 := by
  have hmul : |τ * ell * u * σ| ≤ 1 / 4 := by
    simp only [abs_mul, hell, hσ, mul_one]
    exact (mul_le_mul_of_nonneg_left hu (abs_nonneg τ)).trans (by simpa using hτ)
  have hb := abs_le.mp hmul
  constructor <;> linarith

/-- A bounded cell has a denominator at least twice three quarters to its size. -/
theorem denominator_lower {m : ℕ} {τ : ℝ} {c : Cell m}
    (hτ : |τ| ≤ 1 / 4) (hu : ∀ i, |c.1 i| ≤ 1) :
    2 * (3 / 4 : ℝ) ^ m ≤ denominator τ c := by
  have hl (ell : ℝ) (hell : |ell| = 1) :
      (3 / 4 : ℝ) ^ m ≤ signLikelihood τ c ell := by
    have hs (i : Fin m) : |sign (c.2.1 i)| = 1 := by
      cases c.2.1 i <;> simp [sign]
    simpa only [signLikelihood, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (Finset.prod_le_prod (s := Finset.univ) (f := fun _ : Fin m => (3 / 4 : ℝ))
        (by intros; norm_num)
        (fun i _ => (factor_bounds hτ (hu i) hell (hs i)).1))
  have hp := hl 1 (by norm_num)
  have hn := hl (-1) (by norm_num)
  unfold denominator
  linarith

/-- The posterior denominator is strictly positive for bounded scores and tilt. -/
theorem denominator_pos {m : ℕ} {τ : ℝ} {c : Cell m}
    (hτ : |τ| ≤ 1 / 4) (hu : ∀ i, |c.1 i| ≤ 1) :
    0 < denominator τ c := by
  have h := denominator_lower hτ hu
  have hp : 0 < 2 * (3 / 4 : ℝ) ^ m := by positivity
  linarith

/-- The empty posterior coefficient equals one for bounded scores and tilt. -/
theorem posterior_empty {m : ℕ} {τ : ℝ} {c : Cell m}
    (hτ : |τ| ≤ 1 / 4) (hu : ∀ i, |c.1 i| ≤ 1) :
    posterior τ c ∅ = 1 := by
  have hn := ne_of_gt (denominator_pos hτ hu)
  unfold posterior
  simp only [Finset.prod_empty, mul_one]
  change denominator τ c / denominator τ c = 1
  exact div_self hn

/-- For a positive assignment, the singleton posterior cancels its own likelihood
factor, leaving the difference of the products over the other records. -/
theorem posterior_singleton_cancel {m : ℕ} {τ : ℝ} {c : Cell m}
    (hτ : |τ| ≤ 1 / 4) (hu : ∀ i, |c.1 i| ≤ 1)
    {i : Fin m} (hi : i ∈ active c) :
    posterior τ c {i} = c.1 i *
      ((∏ j ∈ Finset.univ.erase i, (1 + τ * c.1 j * sign (c.2.1 j))) -
       (∏ j ∈ Finset.univ.erase i, (1 - τ * c.1 j * sign (c.2.1 j)))) /
      denominator τ c := by
  have hai : c.2.1 i = true := (Finset.mem_filter.mp hi).2
  have hp : 1 + τ * c.1 i ≠ 0 := by
    have h := (factor_bounds hτ (hu i) (ell := 1) (σ := 1)
      (by norm_num) (by norm_num)).1
    simp only [mul_one] at h
    linarith
  have hn : 1 - τ * c.1 i ≠ 0 := by
    have h := (factor_bounds hτ (hu i) (ell := -1) (σ := 1)
      (by norm_num) (by norm_num)).1
    simp only [mul_one, mul_neg_one, neg_mul] at h
    linarith
  have hsign : sign (c.2.1 i) = 1 := by simp [sign, hai]
  have hplus : signLikelihood τ c 1 = (1 + τ * c.1 i) *
      ∏ j ∈ Finset.univ.erase i, (1 + τ * c.1 j * sign (c.2.1 j)) := by
    simpa only [signLikelihood, mul_one, hsign] using
      (Finset.mul_prod_erase (s := Finset.univ)
        (f := fun j => 1 + τ * c.1 j * sign (c.2.1 j)) (Finset.mem_univ i)).symm
  have hminus : signLikelihood τ c (-1) = (1 - τ * c.1 i) *
      ∏ j ∈ Finset.univ.erase i, (1 - τ * c.1 j * sign (c.2.1 j)) := by
    simpa only [signLikelihood, mul_neg_one, neg_mul, ← sub_eq_add_neg, hsign, mul_one] using
      (Finset.mul_prod_erase (s := Finset.univ)
        (f := fun j => 1 - τ * c.1 j * sign (c.2.1 j)) (Finset.mem_univ i)).symm
  unfold posterior
  simp only [Finset.prod_singleton]
  rw [hplus, hminus]
  congr 1
  field_simp [hp, hn]
  ring

/-- Opposite-sign products differ by at most a linear tilt times the number of factors
and a five-quarters exponential envelope. -/
theorem opposite_products_bound {ι : Type*} (s : Finset ι) (v : ι → ℝ)
    {τ : ℝ} (hτ : |τ| ≤ 1 / 4) (hv : ∀ i ∈ s, |v i| ≤ 1) :
    |(∏ i ∈ s, (1 + τ * v i)) - (∏ i ∈ s, (1 - τ * v i))| ≤
      2 * |τ| * (s.card : ℝ) * (5 / 4 : ℝ) ^ s.card := by
  classical
  have hfactor (i : ι) (hi : i ∈ s) : |1 + τ * v i| ≤ 5 / 4 ∧
      |1 - τ * v i| ≤ 5 / 4 := by
    have hp := factor_bounds hτ (hv i hi) (ell := 1) (σ := 1)
      (by norm_num) (by norm_num)
    have hn := factor_bounds hτ (hv i hi) (ell := -1) (σ := 1)
      (by norm_num) (by norm_num)
    simp only [mul_one, mul_neg_one, neg_mul, ← sub_eq_add_neg] at hp hn
    constructor <;> rw [abs_of_nonneg (by linarith)] <;> linarith
  have hprod (t : Finset ι) (ht : t ⊆ s) :
      |∏ i ∈ t, (1 - τ * v i)| ≤ (5 / 4 : ℝ) ^ t.card := by
    rw [Finset.abs_prod]
    simpa only [Finset.prod_const] using
      (Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i hi => (hfactor i (ht hi)).2))
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    have hva := hv a (Finset.mem_insert_self a t)
    have hvt : ∀ i ∈ t, |v i| ≤ 1 := fun i hi => hv i (Finset.mem_insert_of_mem hi)
    have hd := ih hvt
      (fun i hi => hfactor i (Finset.mem_insert_of_mem hi))
      (fun u hu => hprod u (hu.trans (Finset.subset_insert a t)))
    have hpa := (hfactor a (Finset.mem_insert_self a t)).1
    have hpt := hprod t (Finset.subset_insert a t)
    have hdiff : |2 * τ * v a| ≤ 2 * |τ| := by
      rw [abs_mul, abs_mul]
      norm_num
      exact mul_le_of_le_one_right (by positivity) hva
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
      Nat.cast_add, Nat.cast_one, pow_succ]
    calc
      |(1 + τ * v a) * (∏ i ∈ t, (1 + τ * v i)) -
          (1 - τ * v a) * (∏ i ∈ t, (1 - τ * v i))| =
          |(1 + τ * v a) * ((∏ i ∈ t, (1 + τ * v i)) -
            (∏ i ∈ t, (1 - τ * v i))) +
            (2 * τ * v a) * (∏ i ∈ t, (1 - τ * v i))| := by congr 1; ring
      _ ≤ |1 + τ * v a| * |(∏ i ∈ t, (1 + τ * v i)) -
            (∏ i ∈ t, (1 - τ * v i))| +
            |2 * τ * v a| * |∏ i ∈ t, (1 - τ * v i)| := by
        simpa only [abs_mul] using abs_add_le
          ((1 + τ * v a) * ((∏ i ∈ t, (1 + τ * v i)) -
            (∏ i ∈ t, (1 - τ * v i))))
          ((2 * τ * v a) * (∏ i ∈ t, (1 - τ * v i)))
      _ ≤ (5 / 4) * (2 * |τ| * (t.card : ℝ) * (5 / 4 : ℝ) ^ t.card) +
            (2 * |τ|) * (5 / 4 : ℝ) ^ t.card := by
        exact add_le_add
          (mul_le_mul hpa hd (abs_nonneg _) (by norm_num))
          (mul_le_mul hdiff hpt (abs_nonneg _) (by positivity))
      _ ≤ 2 * |τ| * ((t.card : ℝ) + 1) * ((5 / 4 : ℝ) ^ t.card * (5 / 4)) := by
        have hp : 0 ≤ |τ| * (5 / 4 : ℝ) ^ t.card := by positivity
        nlinarith

/-- A singleton active coefficient is bounded by the tilt times the number of other
records and five thirds to the cell size. -/
theorem posterior_singleton_bound {m : ℕ} {τ : ℝ} {c : Cell m}
    (hτ : |τ| ≤ 1 / 4) (hu : ∀ i, |c.1 i| ≤ 1)
    {i : Fin m} (hi : i ∈ active c) :
    |posterior τ c {i}| ≤ |τ| * ((m - 1 : ℕ) : ℝ) * (5 / 3 : ℝ) ^ m := by
  have hs (j : Fin m) : |sign (c.2.1 j)| = 1 := by
    cases c.2.1 j <;> simp [sign]
  have hv (j : Fin m) : |c.1 j * sign (c.2.1 j)| ≤ 1 := by
    simpa only [abs_mul, hs j, mul_one] using hu j
  have hb := opposite_products_bound (Finset.univ.erase i)
    (fun j => c.1 j * sign (c.2.1 j)) hτ (fun j _ => hv j)
  have hcard : (Finset.univ.erase i).card = m - 1 := by simp
  simp only [hcard, ← mul_assoc] at hb
  have hpow : (5 / 4 : ℝ) ^ (m - 1) ≤ (5 / 4 : ℝ) ^ m :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le m 1)
  have hb' := hb.trans (mul_le_mul_of_nonneg_left hpow
    (by positivity : 0 ≤ 2 * |τ| * ((m - 1 : ℕ) : ℝ)))
  rw [posterior_singleton_cancel hτ hu hi, abs_div, abs_mul,
    abs_of_pos (denominator_pos hτ hu)]
  apply (div_le_iff₀ (denominator_pos hτ hu)).2
  calc
    |c.1 i| * |(∏ j ∈ Finset.univ.erase i, (1 + τ * c.1 j * sign (c.2.1 j))) -
        (∏ j ∈ Finset.univ.erase i, (1 - τ * c.1 j * sign (c.2.1 j)))| ≤
        2 * |τ| * ((m - 1 : ℕ) : ℝ) * (5 / 4 : ℝ) ^ m :=
      (mul_le_of_le_one_left (abs_nonneg _) (hu i)).trans hb'
    _ = (|τ| * ((m - 1 : ℕ) : ℝ) * (5 / 3 : ℝ) ^ m) *
        (2 * (3 / 4 : ℝ) ^ m) := by
      have he : (5 / 3 : ℝ) ^ m * (3 / 4 : ℝ) ^ m = (5 / 4 : ℝ) ^ m := by
        rw [← mul_pow]; norm_num
      calc
        _ = 2 * |τ| * ((m - 1 : ℕ) : ℝ) *
            ((5 / 3 : ℝ) ^ m * (3 / 4 : ℝ) ^ m) := by rw [he]
        _ = _ := by ring
    _ ≤ (|τ| * ((m - 1 : ℕ) : ℝ) * (5 / 3 : ℝ) ^ m) * denominator τ c :=
      mul_le_mul_of_nonneg_left (denominator_lower hτ hu) (by positivity)

/-- A one-record cell has zero active singleton coefficient. -/
theorem posterior_singleton_one {τ : ℝ} {c : Cell 1}
    (hτ : |τ| ≤ 1 / 4) (hu : ∀ i, |c.1 i| ≤ 1)
    {i : Fin 1} (hi : i ∈ active c) : posterior τ c {i} = 0 := by
  have h := posterior_singleton_bound hτ hu hi
  simpa using abs_nonpos_iff.mp (by simpa using h)

/-- Every posterior subset coefficient is bounded by two to its cardinality.
The bound holds even without the active-subset restriction. -/
theorem posterior_subset_bound {m : ℕ} {τ : ℝ} {c : Cell m}
    (hτ : |τ| ≤ 1 / 4) (hu : ∀ i, |c.1 i| ≤ 1) (S : Finset (Fin m)) :
    |posterior τ c S| ≤ (2 : ℝ) ^ S.card := by
  have hf (i : Fin m) : |c.1 i / (1 + τ * c.1 i)| ≤ 2 ∧
      |(-c.1 i) / (1 - τ * c.1 i)| ≤ 2 := by
    have hp := (factor_bounds hτ (hu i) (ell := 1) (σ := 1)
      (by norm_num) (by norm_num)).1
    have hn := (factor_bounds hτ (hu i) (ell := -1) (σ := 1)
      (by norm_num) (by norm_num)).1
    simp only [mul_one, mul_neg_one, neg_mul, ← sub_eq_add_neg] at hp hn
    have hpp : 0 < 1 + τ * c.1 i := by linarith
    have hnp : 0 < 1 - τ * c.1 i := by linarith
    constructor
    · rw [abs_div, abs_of_pos hpp]
      apply (div_le_iff₀ hpp).2
      linarith [hu i]
    · rw [abs_div, abs_neg, abs_of_pos hnp]
      apply (div_le_iff₀ hnp).2
      linarith [hu i]
  have hp : |∏ i ∈ S, c.1 i / (1 + τ * c.1 i)| ≤ (2 : ℝ) ^ S.card := by
    rw [Finset.abs_prod]
    simpa only [Finset.prod_const] using
      (Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => (hf i).1))
  have hn : |∏ i ∈ S, (-c.1 i) / (1 - τ * c.1 i)| ≤ (2 : ℝ) ^ S.card := by
    rw [Finset.abs_prod]
    simpa only [Finset.prod_const] using
      (Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => (hf i).2))
  have hL (ell : ℝ) (hell : |ell| = 1) : 0 ≤ signLikelihood τ c ell := by
    apply Finset.prod_nonneg
    intro i _
    have hs : |sign (c.2.1 i)| = 1 := by cases c.2.1 i <;> simp [sign]
    have h := (factor_bounds hτ (hu i) hell hs).1
    linarith
  have hLp := hL 1 (by norm_num)
  have hLn := hL (-1) (by norm_num)
  unfold posterior
  rw [abs_div, abs_of_pos (denominator_pos hτ hu)]
  apply (div_le_iff₀ (denominator_pos hτ hu)).2
  calc
    _ ≤ |signLikelihood τ c 1 * (∏ i ∈ S, c.1 i / (1 + τ * c.1 i))| +
        |signLikelihood τ c (-1) * (∏ i ∈ S, (-c.1 i) / (1 - τ * c.1 i))| :=
      abs_add_le _ _
    _ = signLikelihood τ c 1 * |∏ i ∈ S, c.1 i / (1 + τ * c.1 i)| +
        signLikelihood τ c (-1) * |∏ i ∈ S, (-c.1 i) / (1 - τ * c.1 i)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hLp, abs_of_nonneg hLn]
    _ ≤ signLikelihood τ c 1 * (2 : ℝ) ^ S.card +
        signLikelihood τ c (-1) * (2 : ℝ) ^ S.card :=
      add_le_add (mul_le_mul_of_nonneg_left hp hLp) (mul_le_mul_of_nonneg_left hn hLn)
    _ = (2 : ℝ) ^ S.card * denominator τ c := by unfold denominator; ring

/-- The order-d energy sums squared posterior coefficients over selected subsets of size d. -/
def subsetEnergy {m : ℕ} (τ : ℝ) (c : Cell m) (d : ℕ) : ℝ :=
  ∑ S ∈ (selected c).powersetCard d, (posterior τ c S) ^ 2

/-- All subset energies are nonnegative. -/
theorem subsetEnergy_nonneg {m : ℕ} (τ : ℝ) (c : Cell m) (d : ℕ) :
    0 ≤ subsetEnergy τ c d := by
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- The order-d energy is bounded by four to d times the cell-size binomial coefficient. -/
theorem subsetEnergy_le_choose {m : ℕ} {τ : ℝ} {c : Cell m}
    (hτ : |τ| ≤ 1 / 4) (hu : ∀ i, |c.1 i| ≤ 1) (d : ℕ) :
    subsetEnergy τ c d ≤ (4 : ℝ) ^ d * (m.choose d : ℝ) := by
  have hcount : ((selected c).powersetCard d).card ≤ m.choose d := by
    simpa only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_le_card (Finset.powersetCard_mono (Finset.subset_univ (selected c))))
  have hterm (S : Finset (Fin m)) (hS : S ∈ (selected c).powersetCard d) :
      (posterior τ c S) ^ 2 ≤ (4 : ℝ) ^ d := by
    have hcard := (Finset.mem_powersetCard.mp hS).2
    have h := (sq_le_sq₀ (abs_nonneg (posterior τ c S))
      (by positivity : 0 ≤ (2 : ℝ) ^ S.card)).2 (posterior_subset_bound hτ hu S)
    rw [sq_abs, ← pow_mul, Nat.mul_comm, pow_mul, hcard] at h
    norm_num at h ⊢
    exact h
  calc
    subsetEnergy τ c d ≤ ∑ S ∈ (selected c).powersetCard d, (4 : ℝ) ^ d :=
      Finset.sum_le_sum hterm
    _ = (((selected c).powersetCard d).card : ℝ) * (4 : ℝ) ^ d := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (m.choose d : ℝ) * (4 : ℝ) ^ d :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (by positivity)
    _ = (4 : ℝ) ^ d * (m.choose d : ℝ) := mul_comm _ _

/-- Given [a tilt τ of absolute value at most 1/4](hyp:hτ) and [valid cell data](hyp:hc)
with m records, [the order-one posterior subset energy is at most
τ² · m · (m − 1)² · (25/9)ᵐ](goal). -/
theorem subsetEnergy_one_bound {m : ℕ} {τ : ℝ} {c : Cell m}
    (hτ : |τ| ≤ 1 / 4) (hc : Valid c) :
    subsetEnergy τ c 1 ≤ τ ^ 2 * (m : ℝ) * ((m - 1 : ℕ) : ℝ) ^ 2 *
      ((5 / 3 : ℝ) ^ 2) ^ m := by
  have hcount : ((selected c).powersetCard 1).card ≤ m := by
    simpa only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
      Nat.choose_one_right] using
      (Finset.card_le_card (Finset.powersetCard_mono (n := 1) (Finset.subset_univ (selected c))))
  have hterm (S : Finset (Fin m)) (hS : S ∈ (selected c).powersetCard 1) :
      (posterior τ c S) ^ 2 ≤ τ ^ 2 * ((m - 1 : ℕ) : ℝ) ^ 2 *
        ((5 / 3 : ℝ) ^ 2) ^ m := by
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp (Finset.mem_powersetCard.mp hS).2
    have hi : i ∈ active c := hc.2 ((Finset.mem_powersetCard.mp hS).1 (by simp))
    have h := (sq_le_sq₀ (abs_nonneg (posterior τ c {i}))
      (by positivity : 0 ≤ |τ| * ((m - 1 : ℕ) : ℝ) * (5 / 3 : ℝ) ^ m)).2
      (posterior_singleton_bound hτ hc.1 hi)
    simpa only [mul_pow, sq_abs, ← pow_mul, Nat.mul_comm] using h
  calc
    subsetEnergy τ c 1 ≤ ∑ S ∈ (selected c).powersetCard 1,
        τ ^ 2 * ((m - 1 : ℕ) : ℝ) ^ 2 * ((5 / 3 : ℝ) ^ 2) ^ m :=
      Finset.sum_le_sum hterm
    _ = (((selected c).powersetCard 1).card : ℝ) *
        (τ ^ 2 * ((m - 1 : ℕ) : ℝ) ^ 2 * ((5 / 3 : ℝ) ^ 2) ^ m) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (m : ℝ) * (τ ^ 2 * ((m - 1 : ℕ) : ℝ) ^ 2 * ((5 / 3 : ℝ) ^ 2) ^ m) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (by positivity)
    _ = τ ^ 2 * (m : ℝ) * ((m - 1 : ℕ) : ℝ) ^ 2 * ((5 / 3 : ℝ) ^ 2) ^ m := by ring

/-- Each fixed-order subset energy is measurable as a function of the cell data. -/
@[fun_prop] theorem measurable_subsetEnergy (m d : ℕ) (τ : ℝ) :
    Measurable (fun c : Cell m => subsetEnergy τ c d) := by
  classical
  have hsign : Measurable sign := measurable_of_countable sign
  have hp (S : Finset (Fin m)) : Measurable (fun c : Cell m => (posterior τ c S) ^ 2) := by
    unfold posterior denominator signLikelihood
    fun_prop
  have hsel (S : Finset (Fin m)) : MeasurableSet {c : Cell m | S ⊆ selected c} := by
    have hflags : Measurable (fun c : Cell m => c.2.2) := measurable_snd.comp measurable_snd
    have hset : MeasurableSet {b : Fin m → Bool |
        S ⊆ Finset.univ.filter (fun i => b i = true)} := (Set.to_countable _).measurableSet
    exact hset.preimage hflags
  have heq (c : Cell m) : subsetEnergy τ c d =
      ∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard d,
        if S ⊆ selected c then (posterior τ c S) ^ 2 else 0 := by
    rw [← Finset.sum_filter]
    unfold subsetEnergy
    congr 1
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    exact and_comm
  simp_rw [heq]
  apply Finset.measurable_sum
  intro S _
  exact Measurable.ite (hsel S) (hp S) measurable_const

end Causalean.Stat.Minimax.Mixture.PoissonLatentSign
