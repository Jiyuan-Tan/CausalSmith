module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedConstruction

/-! # Cardinality bounds for active folded cells -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

private lemma active_first_index_nat (q t : ℕ) (hq : 24 ≤ q) (ht : t < q / 8) :
    q ≤ 3 * ((q + 2) / 3 + t) ∧
      3 * (((q + 2) / 3 + t) + 1) ≤ 2 * q ∧
      (q + 2) / 3 + t < q := by
  omega

private lemma active_first_index_real (q t : ℕ) (hq : 24 ≤ q) (ht : t < q / 8) :
    (1 / 3 : ℝ) ≤ (((q + 2) / 3 + t : ℕ) : ℝ) / q ∧
      ((((q + 2) / 3 + t : ℕ) : ℝ) + 1) / q ≤ (2 / 3 : ℝ) := by
  have hn := active_first_index_nat q t hq ht
  have hqR : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 24) hq)
  constructor
  · apply (le_div_iff₀ hqR).2
    have hcast : (q : ℝ) ≤ 3 * (((q + 2) / 3 + t : ℕ) : ℝ) := by
      exact_mod_cast hn.1
    linarith
  · apply (div_le_iff₀ hqR).2
    have hcast : 3 * (((((q + 2) / 3 + t : ℕ) : ℝ) + 1)) ≤ 2 * (q : ℝ) := by
      exact_mod_cast hn.2.1
    linarith

private lemma card_nonzero_fin_coordinates (d : ℕ) (hd : 0 < d) :
    Fintype.card {i : Fin d // i.val ≠ 0} = d - 1 := by
  rw [Fintype.card_subtype_compl]
  have hz : Fintype.card {i : Fin d // i.val = 0} = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨⟨⟨0, hd⟩, rfl⟩, ?_⟩
    intro i
    apply Subtype.ext
    apply Fin.ext
    exact i.property
  rw [hz]
  simp

lemma FoldedGeometry.card_lower {hd : 0 < d} {q K : ℕ}
    {Q : Fin K → Set (XSpace d)} {ψ : Fin K → XSpace d → ℝ}
    {B : Fin K → Set (XSpace d)}
    (hgeo : FoldedGeometry hd q K Q ψ B) (hq : 24 ≤ q) :
    (q / 8) * q ^ (d - 1) ≤ K := by
  classical
  rcases hgeo with ⟨hqpos, k, hkinj, hcomplete, hdefs⟩
  let Tail := {i : Fin d // i.val ≠ 0}
  let Source := Fin (q / 8) × (Tail → Fin q)
  let v : Source → Fin d → ℕ := fun z i =>
    if hi : i.val = 0 then (q + 2) / 3 + z.1.val
    else (z.2 ⟨i, hi⟩).val
  have hvactive (z : Source) : activeMeshCell hd q (v z) := by
    have hfirst := active_first_index_real q z.1.val hq z.1.isLt
    refine ⟨?_, ?_, ?_⟩
    · intro i
      by_cases hi : i.val = 0
      · simp only [v, dif_pos hi]
        exact (active_first_index_nat q z.1.val hq z.1.isLt).2.2
      · simp only [v, dif_neg hi]
        exact (z.2 ⟨i, hi⟩).isLt
    · simpa [v] using hfirst.1
    · simpa [v] using hfirst.2
  let pick : Source → Fin K := fun z => Classical.choose ((hcomplete (v z)).1 (hvactive z))
  have hpick (z : Source) : k (pick z) = v z :=
    Classical.choose_spec ((hcomplete (v z)).1 (hvactive z))
  have hinj : Function.Injective pick := by
    intro z w hzw
    have hvw : v z = v w := by rw [← hpick z, ← hpick w, hzw]
    apply Prod.ext
    · apply Fin.ext
      have h0 := congrFun hvw ⟨0, hd⟩
      simpa [v] using h0
    · funext i
      apply Fin.ext
      have hi := congrFun hvw i.1
      simpa [v, i.2] using hi
  have hcard : Fintype.card Source ≤ Fintype.card (Fin K) :=
    Fintype.card_le_of_injective pick hinj
  change (q / 8) * q ^ (d - 1) ≤ K
  simpa [Source, Tail, Fintype.card_prod, Fintype.card_pi,
    card_nonzero_fin_coordinates d hd] using hcard

lemma FoldedGeometry.card_upper {hd : 0 < d} {q K : ℕ}
    {Q : Fin K → Set (XSpace d)} {ψ : Fin K → XSpace d → ℝ}
    {B : Fin K → Set (XSpace d)}
    (hgeo : FoldedGeometry hd q K Q ψ B) : K ≤ q ^ d := by
  classical
  rcases hgeo with ⟨hq, k, hkinj, hcomplete, hdefs⟩
  let f : Fin K → (Fin d → Fin q) := fun j i =>
    ⟨k j i, ((hcomplete (k j)).2 ⟨j, rfl⟩).1 i⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply hkinj
    funext r
    exact congrArg Fin.val (congrFun hij r)
  have := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_pi] using this

end CausalSmith.Experimentation.PilotscorePairingFrontier
