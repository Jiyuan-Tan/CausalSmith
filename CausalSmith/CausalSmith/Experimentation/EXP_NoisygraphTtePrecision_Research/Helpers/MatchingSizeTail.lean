module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.MatchingPosterior
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Counting matchings and the dilute-prior lower tail

Matchings of a fixed size correspond to a recipient subset and an injection into
the donor set. Consecutive size weights grow geometrically below twice the threshold.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false

/-- The recipients assigned a donor by a partial matching. -/
-- @node: matchingRecipients
def matchingRecipients {m : ℕ} (M : Matching m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => (M.1 i).isSome)

/-- [Counting edges is the same as counting matched recipients.](goal) -/
-- @node: matchingRecipients_card
lemma matchingRecipients_card {m : ℕ} (M : Matching m) :
    (matchingRecipients M).card = M.size := by
  symm
  apply Finset.card_bij (fun e _ => e.2)
  · intro e he
    have h := (Finset.mem_filter.mp he).2
    simp [matchingRecipients, h]
  · intro e he e' he' h
    apply Prod.ext _ h
    exact Option.some.inj (((Finset.mem_filter.mp he).2).symm.trans
      (h ▸ (Finset.mem_filter.mp he').2))
  · intro i hi
    have hi' : (M.1 i).isSome := (Finset.mem_filter.mp hi).2
    cases h : M.1 i with
    | none => simp [h] at hi'
    | some j => exact ⟨(j,i), by simp [Matching.edges, h], rfl⟩

/-- Read the unique donor at each matched recipient as an injection. -/
-- @node: matchingRecipientEmbedding
def matchingRecipientEmbedding {m : ℕ} (M : Matching m) :
    ↥(matchingRecipients M) ↪ Fin m where
  toFun i := (M.1 i.1).get (by simpa [matchingRecipients] using i.2)
  inj' := by
    intro i j hij
    apply Subtype.ext
    exact M.2 i j _ (Option.some_get _).symm
      ((Option.some_get _).symm.trans (congrArg some hij.symm))

/-- Reconstruct a matching from its recipient set and its injective donor assignment. -/
-- @node: matchingFromEmbedding
def matchingFromEmbedding {m : ℕ} (S : Finset (Fin m)) (e : ↥S ↪ Fin m) : Matching m :=
  ⟨fun i => if hi : i ∈ S then some (e ⟨i,hi⟩) else none, by
    intro i j a hi hj
    dsimp only at hi hj
    split_ifs at hi with hI
    split_ifs at hj with hJ
    exact congrArg Subtype.val (e.injective ((Option.some.inj hi).trans (Option.some.inj hj).symm))⟩

/-- [Reconstruction recovers exactly the declared recipient set.](goal) -/
-- @node: matchingFromEmbedding_recipients
lemma matchingFromEmbedding_recipients {m : ℕ} (S : Finset (Fin m)) (e : ↥S ↪ Fin m) :
    matchingRecipients (matchingFromEmbedding S e) = S := by
  ext i
  simp [matchingRecipients, matchingFromEmbedding]

/-- [Reconstruction consequently has the prescribed number of arrows.](goal) -/
-- @node: matchingFromEmbedding_size
lemma matchingFromEmbedding_size {m : ℕ} (S : Finset (Fin m)) (e : ↥S ↪ Fin m) :
    (matchingFromEmbedding S e).size = S.card := by
  rw [← matchingRecipients_card, matchingFromEmbedding_recipients]

/-- Fixed-size matchings are enumerated by recipient subsets and injections into donors. -/
-- @node: matchingSizeEquiv
def matchingSizeEquiv (m k : ℕ) :
    {M : Matching m // M.size = k} ≃
      (Σ S : {S : Finset (Fin m) // S.card = k}, ↥S.1 ↪ Fin m) :=
  Equiv.ofBijective
    (fun p => ⟨matchingFromEmbedding p.1.1 p.2,
      (matchingFromEmbedding_size _ _).trans p.1.2⟩)
    (by
      constructor
      · intro p q h
        have hM := congrArg Subtype.val h
        have hS : p.1 = q.1 := by
          apply Subtype.ext
          simpa only [matchingFromEmbedding_recipients] using congrArg matchingRecipients hM
        cases p with
        | mk S e =>
          cases q with
          | mk T f =>
            dsimp only at hS
            subst T
            congr 1
            apply DFunLike.ext
            intro i
            have hi := congrArg (fun M : Matching m => M.1 i.1) hM
            simpa [matchingFromEmbedding, i.2] using hi
      · intro M
        refine ⟨⟨⟨matchingRecipients M.1, (matchingRecipients_card _).trans M.2⟩,
          matchingRecipientEmbedding M.1⟩, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        funext i
        dsimp only [matchingFromEmbedding]
        split_ifs with hi
        · exact Option.some_get _
        · have hn : ¬ (M.1.1 i).isSome := by simpa [matchingRecipients] using hi
          cases h : M.1.1 i <;> simp_all)
    |>.symm

/-- [Choosing recipients and then their injective donor map counts the size class.](goal) -/
-- @node: matching_size_count
lemma matching_size_count (m k : ℕ) :
    Fintype.card {M : Matching m // M.size = k} = m.choose k ^ 2 * k.factorial := by
  rw [Fintype.card_congr (matchingSizeEquiv m k), Fintype.card_sigma]
  have hcard : Fintype.card {S : Finset (Fin m) // S.card = k} = m.choose k := by
    classical
    have he : {S : Finset (Fin m) // S.card = k} ≃ ↥(Finset.univ.powersetCard k) :=
      Equiv.subtypeEquivRight (fun S => by simp)
    rw [Fintype.card_congr he, Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin]
  simp only [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe]
  simp_rw [show ∀ S : {S : Finset (Fin m) // S.card = k}, S.1.card = k from fun S => S.2]
  rw [Finset.sum_const, Finset.card_univ, hcard, Nat.nsmul_eq_mul,
    Nat.descFactorial_eq_factorial_mul_choose]
  ring


/-- The unnormalized total weight of the matchings with a prescribed size. -/
-- @node: matchingSizeWeight
def matchingSizeWeight (m k : ℕ) : ℝ :=
  (m.choose k : ℝ)^2 * (k.factorial : ℝ) * activity m ^ k

/-- [The size count identifies each fiber's weight sum.](goal) -/
-- @node: matching_size_weight_sum
lemma matching_size_weight_sum (m k : ℕ) :
    (∑ M ∈ Finset.univ.filter (fun M : Matching m => M.size = k), matchingWeight m M) =
      matchingSizeWeight m k := by
  have hc : (Finset.univ.filter (fun M : Matching m => M.size = k)).card =
      m.choose k ^ 2 * k.factorial := by
    rw [← Fintype.card_subtype, matching_size_count]
  rw [Finset.sum_congr rfl (fun M hM => show matchingWeight m M = activity m ^ k by
    rw [matchingWeight, (Finset.mem_filter.mp hM).2]), Finset.sum_const, nsmul_eq_mul, hc]
  simp [matchingSizeWeight, Nat.cast_mul, Nat.cast_pow]

/-- [Partitioning all matchings by size expresses the normalizer as the size-weight sum.](goal) -/
-- @node: matchingPartition_size_sum
lemma matchingPartition_size_sum (m : ℕ) :
    matchingPartition m = ∑ k ∈ Finset.range (m+1), matchingSizeWeight m k := by
  rw [matchingPartition, ← Finset.sum_fiberwise_of_maps_to
    (g := fun M : Matching m => M.size) (t := Finset.range (m+1))
    (fun M _ => Finset.mem_range.mpr (by have := matching_size_le m M; omega))]
  simp_rw [matching_size_weight_sum]

/-- [The lower-size event is a normalized prefix of the finite size weights.](goal) -/
-- @node: matchingPrior_size_tail_eq
lemma matchingPrior_size_tail_eq (m k : ℕ) :
    (matchingPrior m).real {M | M.size < k} =
      (∑ j ∈ Finset.range k, matchingSizeWeight m j) / matchingPartition m := by
  have hsum : (∑ M : Matching m, if M.size < k then matchingWeight m M else 0) =
      ∑ j ∈ Finset.range k, matchingSizeWeight m j := by
    have h := Finset.sum_fiberwise_eq_sum_filter
      Finset.univ (Finset.range k) (fun M : Matching m => M.size) (matchingWeight m)
    simp only [Finset.mem_range, matching_size_weight_sum] at h
    simpa only [Finset.sum_filter] using h.symm
  unfold Measure.real matchingPrior
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (MeasurableSet.of_discrete), Set.indicator_apply, Pi.one_apply,
    Set.mem_ofPred_eq]
  simp_rw [mul_ite, mul_one, mul_zero, ← ENNReal.ofReal_zero,
    ← apply_ite ENNReal.ofReal]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun M _ => by
    split_ifs <;> first | exact matchingPriorMass_nonneg m M | exact le_rfl),
    ENNReal.toReal_ofReal (Finset.sum_nonneg (fun M _ => by
      split_ifs <;> first | exact matchingPriorMass_nonneg m M | exact le_rfl))]
  simpa only [matchingPriorMass, Finset.sum_div, ite_div, zero_div] using
    congrArg (fun x : ℝ => x / matchingPartition m) hsum

/-- [Size weights are nonnegative.](goal) -/
-- @node: matchingSizeWeight_nonneg
lemma matchingSizeWeight_nonneg (m k : ℕ) : 0 ≤ matchingSizeWeight m k := by
  unfold matchingSizeWeight activity
  positivity

/-- Given [the stated assumptions](hyp:hk), [The binomial successor identity gives the exact consecutive-weight relation.](goal) -/
-- @node: matchingSizeWeight_step
lemma matchingSizeWeight_step (m k : ℕ) (hk : k < m) :
    matchingSizeWeight m (k+1) * (4*(m : ℝ)*(k+1)) =
      matchingSizeWeight m k * ((m : ℝ)-k)^2 := by
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hc : (m.choose (k+1) : ℝ) * ((k : ℝ)+1) =
      (m.choose k : ℝ) * ((m : ℝ)-k) := by
    have h := Nat.choose_succ_right_eq m k
    have hR := congrArg (fun x : ℕ => (x : ℝ)) h
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hk.le] using hR
  have hk1 : (k : ℝ)+1 ≠ 0 := by positivity
  have hc' := (eq_div_iff hk1).mpr hc
  simp only [matchingSizeWeight, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, pow_succ, activity]
  rw [hc']
  field_simp

/-- Given [the stated assumptions](hyp:hm,hk), [Below twice the threshold, each consecutive size weight grows by at least four.](goal) -/
-- @node: matchingSizeWeight_ge_four
lemma matchingSizeWeight_ge_four (m k : ℕ) (hm : 256 ≤ m) (hk : k < 2 * kZero m) :
    4 * matchingSizeWeight m k ≤ matchingSizeWeight m (k+1) := by
  have hkN : 32*(k+1) ≤ m := by dsimp [kZero] at hk; omega
  have hkm : k < m := by omega
  have hkR : 32*((k : ℝ)+1) ≤ m := by exact_mod_cast hkN
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hgap : 0 ≤ (m : ℝ)-k := by linarith
  have hratio : 4*(4*(m : ℝ)*(k+1)) ≤ ((m : ℝ)-k)^2 := by
    nlinarith [sq_nonneg ((m : ℝ)-k),
      mul_nonneg hmR.le (sub_nonneg.mpr hkR)]
  have hw := matchingSizeWeight_nonneg m k
  have he := matchingSizeWeight_step m k hkm
  have hden : 0 < 4*(m : ℝ)*(k+1) := by positivity
  apply (mul_le_mul_iff_left₀ hden).mp
  nlinarith [mul_nonneg hw (sub_nonneg.mpr hratio)]

/-- Given [the stated assumptions](hyp:hm,hjt), [Iterating the consecutive-weight bound transports each prefix weight above the threshold.](goal) -/
-- @node: matchingSizeWeight_shift
lemma matchingSizeWeight_shift (m j t : ℕ) (hm : 256 ≤ m)
    (hjt : j + t ≤ 2 * kZero m) :
    4^t * matchingSizeWeight m j ≤ matchingSizeWeight m (j + t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have ih' := ih (by omega)
    have hs := matchingSizeWeight_ge_four m (j + t) hm (by omega)
    calc
      4^(t+1) * matchingSizeWeight m j = 4*(4^t * matchingSizeWeight m j) := by ring
      _ ≤ 4 * matchingSizeWeight m (j + t) := mul_le_mul_of_nonneg_left ih' (by norm_num)
      _ ≤ matchingSizeWeight m (j+(t+1)) := by simpa [Nat.add_assoc] using hs


/-- Given [the stated assumptions](hyp:hm), [The shifted prefix is a distinct subset of the normalizer, yielding the geometric tail.](goal) -/
-- @node: matchingPrior_size_tail_bound
lemma matchingPrior_size_tail_bound (m : ℕ) (hm : 256 ≤ m) :
    (matchingPrior m).real {M | M.size < kZero m} ≤ (4 : ℝ)⁻¹ ^ kZero m := by
  let k := kZero m
  have hshift : (4 : ℝ)^k * (∑ j ∈ Finset.range k, matchingSizeWeight m j) ≤
      ∑ j ∈ Finset.range k, matchingSizeWeight m (j+k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    exact matchingSizeWeight_shift m j k hm (by have := Finset.mem_range.mp hj; omega)
  have hsub : (Finset.range k).image (fun j => j+k) ⊆ Finset.range (m+1) := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have hi' := Finset.mem_range.mp hi
    dsimp [k, kZero] at *
    apply Finset.mem_range.mpr
    omega
  have hpart : (∑ j ∈ Finset.range k, matchingSizeWeight m (j+k)) ≤ matchingPartition m := by
    rw [matchingPartition_size_sum]
    rw [← Finset.sum_image (fun a _ b _ h => by omega)]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => matchingSizeWeight_nonneg m j)
  have hprefix : (∑ j ∈ Finset.range k, matchingSizeWeight m j) ≤
      matchingPartition m / (4 : ℝ)^k := by
    apply (le_div_iff₀ (by positivity : 0 < (4 : ℝ)^k)).mpr
    simpa only [mul_comm] using hshift.trans hpart
  rw [matchingPrior_size_tail_eq]
  calc
    _ ≤ (matchingPartition m / (4 : ℝ)^k) / matchingPartition m :=
      div_le_div_of_nonneg_right hprefix (matchingPartition_pos m).le
    _ = (4 : ℝ)⁻¹ ^ k := by
      rw [inv_pow]
      field_simp
      exact div_self (ne_of_gt (matchingPartition_pos m))

end CausalSmith.Experimentation.NoisygraphTtePrecision
