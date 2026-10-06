module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.NormalizedSmallN

/-! # Glue interface for the two branches of the normalized converse -/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory

-- @node: def:normalized-certificate
/-- The paired-prior conclusion at fixed parameters and separation constant. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `c`](hyp:c), [the stated mathematical conclusion holds](goal). Given [the specified input `β`](hyp:β). -/
def NormalizedCertificate (n d : ℕ) (q β c : ℝ) : Prop :=
  ∃ πminus πplus : PMF (ClassLaw d q),
    Causalean.Stat.tvDist
      (priorPredictive n d q πminus)
      (priorPredictive n d q πplus) ≤ β ∧
    ∃ m0 : ℝ,
      1 - β ≤ priorEventMass d q πminus
        (fun P => tau P.val ≤ m0 - c * gScale n d q) ∧
      1 - β ≤ priorEventMass d q πplus
        (fun P => m0 + c * gScale n d q ≤ tau P.val)

-- @node: def:eventual-normalized-certificate
/-- The exact remaining large-sample obligation: a uniform certificate after
a threshold depending only on the fixed testing tolerance. [the stated mathematical conclusion holds](goal). Given [the specified input `β`](hyp:β). -/
def EventualNormalizedCertificate (β : ℝ) : Prop :=
  ∃ N : ℕ, 2 ≤ N ∧ ∃ cLarge : ℝ, 0 < cLarge ∧
    ∀ (n d : ℕ) (q : ℝ), N ≤ n → 1 ≤ d →
      q ∈ Set.Icc ((1 : ℝ) / 2) 1 →
      gScale n d q ^ 2 ≥ 1 / (n : ℝ) →
      NormalizedCertificate n d q β cLarge

-- @node: normalizedCertificate_mono
/-- A certificate remains valid after decreasing its separation constant. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `c`](hyp:c), [the specified input `c'`](hyp:c'), [the specified input `hc`](hyp:hc), [the specified input `hcc`](hyp:hcc), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `β`](hyp:β). Given [the specified input `hq`](hyp:hq). -/
lemma normalizedCertificate_mono {n d : ℕ} {q β c c' : ℝ}
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) (hc : 0 ≤ c) (hcc : c ≤ c')
    (h : NormalizedCertificate n d q β c') :
    NormalizedCertificate n d q β c := by
  have hdelta : 0 ≤ delta q := by simp [delta]; linarith [hq.2]
  have hratio : 0 ≤ (d : ℝ) / ((n : ℝ) * ell n) := by
    exact div_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (le_of_lt (ell_pos_for_normalization n)))
  have hg : 0 ≤ gScale n d q := by
    exact mul_nonneg hdelta (le_min (by norm_num) hratio)
  obtain ⟨πminus, πplus, htv, m0, hminus, hplus⟩ := h
  refine ⟨πminus, πplus, htv, m0, ?_, ?_⟩
  · apply hminus.trans
    unfold priorEventMass
    refine measureReal_mono ?_ (by finiteness)
    intro P hP
    dsimp at hP ⊢
    nlinarith [mul_le_mul_of_nonneg_right hcc hg]
  · apply hplus.trans
    unfold priorEventMass
    refine measureReal_mono ?_ (by finiteness)
    intro P hP
    dsimp at hP ⊢
    nlinarith [mul_le_mul_of_nonneg_right hcc hg]

-- @node: normalized_converse_of_eventual_certificate
/-- An eventual uniform certificate and the parametric finite branch imply the
full normalized converse. Given [the specified input `hlarge`](hyp:hlarge), [the stated mathematical conclusion holds](goal). Given [the specified input `β`](hyp:β). Given [the specified input `hβ`](hyp:hβ). -/
lemma normalized_converse_of_eventual_certificate (β : ℝ)
    (hβ : β ∈ Set.Ioo 0 ((1 : ℝ) / 4))
    (hlarge : EventualNormalizedCertificate β) :
    ∃ cβ : ℝ, 0 < cβ ∧
      ∀ (n d : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ d →
        q ∈ Set.Icc ((1 : ℝ) / 2) 1 →
        gScale n d q ^ 2 ≥ 1 / (n : ℝ) →
        NormalizedCertificate n d q β cβ := by
  obtain ⟨N, hN, cLarge, hcLarge, hlarge⟩ := hlarge
  have hb : 0 < 2 * β := by linarith [hβ.1]
  obtain ⟨a, ha, hbudget⟩ := parametric_radius_budget_at_tolerance (2 * β) hb
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hrootN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
  let cSmall := a / Real.sqrt N
  let cβ := min cLarge cSmall
  have hcSmall : 0 < cSmall := by dsimp [cSmall]; positivity
  have hcβ : 0 < cβ := by exact lt_min hcLarge hcSmall
  refine ⟨cβ, hcβ, ?_⟩
  intro n d q hn hd hq hg
  by_cases hnLarge : N ≤ n
  · apply normalizedCertificate_mono hq (le_of_lt hcβ) (min_le_left _ _)
    exact hlarge n d q hnLarge hd hq hg
  · have hnSmall : n < N := Nat.lt_of_not_ge hnLarge
    apply normalizedCertificate_mono hq (le_of_lt hcβ) (min_le_right _ _)
    exact normalized_converse_smallN hβ.1 ha hbudget hn hnSmall hd hq

end CausalSmith.Stat.MarNearcompleteFrontier
