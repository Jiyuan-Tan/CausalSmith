module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.Estimator

/-! # Exact deterministic four-block partition -/

@[expose] public section
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength
/-- Given [the supplied inputs](hyp:n,b), [the stated result about block card holds](goal). -/

lemma block_card (n : ℕ) (b : Fin 4) :
    (blockIdx n b).card = blockSize n b := by
  let lo := b.val * n / 4
  let hi := (b.val + 1) * n / 4
  have hprodlo : b.val * n ≤ (b.val + 1) * n :=
    Nat.mul_le_mul_right n (by omega)
  have hprodhi : (b.val + 1) * n ≤ 4 * n :=
    Nat.mul_le_mul_right n (by omega)
  have hlo : lo ≤ hi := by dsimp [lo, hi]; omega
  have hhi : hi ≤ n := by
    have hb := b.isLt
    dsimp [hi]
    omega
  have hsub : (Finset.univ.filter (fun i : Fin n => i.val < lo)) ⊆
      (Finset.univ.filter (fun i : Fin n => i.val < hi)) := by
    intro i hi'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' ⊢
    omega
  have heq : blockIdx n b =
      (Finset.univ.filter (fun i : Fin n => i.val < hi)) \
        (Finset.univ.filter (fun i : Fin n => i.val < lo)) := by
    ext i
    simp [blockIdx, lo, hi]
    omega
  rw [heq, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
  rw [Fin.card_filter_val_lt, Fin.card_filter_val_lt]
  simp [Nat.min_eq_right hhi, Nat.min_eq_right (le_trans hlo hhi),
    blockSize, lo, hi]
/-- Given [the supplied inputs](hyp:n,hn,b), [the stated result about block size lower holds](goal). -/

lemma block_size_lower (n : ℕ) (hn : threshold ≤ n) (b : Fin 4) :
    (n : ℝ) / 5 ≤ blockSize n b := by
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 5)).2
  norm_cast
  norm_num [threshold] at hn
  fin_cases b <;> simp only [blockSize] <;> omega
/-- [The training view object](goal) is defined from [the supplied inputs](hyp:n). -/

def trainingView {n : ℕ} (ω : TwoSample n n) : TwoSample n n :=
  ((fun i => if i ∈ blockIdx n 0 then ω.1 i else (0, false, false, 0)),
   (fun i => if i ∈ blockIdx n 0 then ω.2 i else 0))
/-- [The training sigma object](goal) is defined from [the supplied inputs](hyp:n). -/

abbrev trainingSigma (n : ℕ) : MeasurableSpace (TwoSample n n) :=
  MeasurableSpace.comap trainingView inferInstance

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
