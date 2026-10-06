module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Basic
public import Causalean.Stat.Concentration.TailBounds.Hoeffding
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Separated binary codes at logarithmic length

A fair product stream and Hoeffding union bound give an injective family of
`M` Boolean words with pairwise Hamming distance at least one quarter of the
chosen logarithmic code length.
-/

@[expose] public section

set_option linter.style.longLine false

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
/-- [the code dimension quantity](goal) is defined from [the candidate-policy count](hyp:M). -/
noncomputable def codeDimension (M : Nat) : Nat := Nat.ceil (24 * Real.log (M : ℝ))
  -- @realizes CodeV(code dimension of order log M)

-- @node: codeDimension_pos
/-- For [the candidate-policy count](hyp:M) and [the candidate-policy count assumption](hyp:hM),
this establishes [the code dimension positivity result](goal). -/
lemma codeDimension_pos (M : Nat) (hM : 2 ≤ M) : 0 < codeDimension M := by
  unfold codeDimension
  apply Nat.ceil_pos.mpr
  have hM' : (1 : ℝ) < M := by exact_mod_cast hM
  exact mul_pos (by norm_num) (Real.log_pos hM')

/-- The code length is large enough for the pairwise union bound in the probabilistic packing
construction. For [the candidate-policy count](hyp:M), this establishes
[the code dimension log lower result](goal). -/
-- @node: codeDimension_log_lower
lemma codeDimension_log_lower (M : Nat) :
    24 * Real.log (M : ℝ) ≤ (codeDimension M : ℝ) := by
  unfold codeDimension
  exact Nat.le_ceil _

/-- The union bound over all ordered pairs is below one at the chosen logarithmic code length.
For [the candidate-policy count](hyp:M) and [the candidate-policy count assumption](hyp:hM),
this establishes [the code dimension pair union bound result](goal). -/
-- @node: codeDimension_pair_union_bound
lemma codeDimension_pair_union_bound (M : Nat) (hM : 2 ≤ M) :
    (M : ℝ) ^ 2 * Real.exp (-(codeDimension M : ℝ) / 8) ≤ 1 / M := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hexp : Real.exp (-(codeDimension M : ℝ) / 8) ≤
      Real.exp (-3 * Real.log (M : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hd := codeDimension_log_lower M
    linarith
  have hpow : Real.exp (-3 * Real.log (M : ℝ)) = (M : ℝ)⁻¹ ^ 3 := by
    have harg : -3 * Real.log (M : ℝ) = (3 : ℕ) * (-Real.log (M : ℝ)) := by ring
    rw [harg, Real.exp_nat_mul, Real.exp_neg, Real.exp_log hMpos]
  calc
    (M : ℝ) ^ 2 * Real.exp (-(codeDimension M : ℝ) / 8) ≤
        (M : ℝ) ^ 2 * Real.exp (-3 * Real.log (M : ℝ)) :=
          mul_le_mul_of_nonneg_left hexp (sq_nonneg _)
    _ = 1 / M := by rw [hpow]; field_simp
/-- [the hamming distance quantity](goal) is defined from [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the binary code](hyp:code), [the codeword index](hyp:v), and
[the observed word](hyp:w). -/

def hammingDistance {M d : Nat} (code : Fin M → Fin d → Bool)
    (v w : Fin M) : Nat :=
  (Finset.univ.filter (fun i : Fin d ↦ code v i ≠ code w i)).card
/-- [the code separated predicate](goal) is defined from [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), and [the binary code](hyp:code). -/

def CodeSeparated {M d : Nat} (code : Fin M → Fin d → Bool) : Prop :=
  Function.Injective code ∧
    ∀ v w : Fin M, v ≠ w → (d : ℝ) / 4 ≤ hammingDistance code v w
  -- @realizes CodeV(binary code with pairwise distance at least d/4)

private noncomputable def fairWordLaw (M : Nat) : Measure (Fin M → Bool) :=
  (PMF.uniformOfFintype (Fin M → Bool)).toMeasure

private noncomputable def fairWordSample (M : Nat) :
    Causalean.Stat.IIDSample
      (ℕ → (Fin M → Bool)) (Fin M → Bool)
      (Measure.infinitePi (fun _ : ℕ ↦ fairWordLaw M)) (fairWordLaw M) := by
  letI : IsProbabilityMeasure (fairWordLaw M) :=
    PMF.toMeasure.isProbabilityMeasure (PMF.uniformOfFintype (Fin M → Bool))
  exact {
    Z := fun i ω ↦ ω i
    meas := fun i ↦ measurable_pi_apply i
    indep := iIndepFun_infinitePi (X := fun _ (ω : Fin M → Bool) ↦ ω)
      (fun _ ↦ measurable_id)
    identDist := fun i ↦ ⟨
      (measurePreserving_eval_infinitePi
        (fun _ : ℕ ↦ fairWordLaw M) 0).measurable.aemeasurable,
      (measurePreserving_eval_infinitePi
        (fun _ : ℕ ↦ fairWordLaw M) i).measurable.aemeasurable,
      by rw [
        (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ fairWordLaw M) 0).map_eq,
        (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ fairWordLaw M) i).map_eq]⟩
    law := (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ fairWordLaw M) 0).map_eq }

private lemma fairWordLaw_disagreement_mean {M : Nat} (v w : Fin M) (hvw : v ≠ w) :
    ∫ word, (if word v ≠ word w then 1 else 0 : ℝ) ∂fairWordLaw M = 1 / 2 := by
  classical
  unfold fairWordLaw
  rw [PMF.integral_eq_sum]
  simp [PMF.uniformOfFintype_apply]
  let flipAt : (Fin M → Bool) → (Fin M → Bool) :=
    fun word ↦ Function.update word v (!word v)
  have hflip : Function.Involutive flipAt := by
    intro word
    funext i
    by_cases hiv : i = v
    · subst i
      simp [flipAt]
    · simp [flipAt, hiv]
  let e : (Fin M → Bool) ≃ (Fin M → Bool) :=
    { toFun := flipAt
      invFun := flipAt
      left_inv := hflip
      right_inv := hflip }
  let c : ℝ := ((2 : ℝ) ^ M)⁻¹
  have hswap :
      (∑ word : Fin M → Bool, if word v = word w then 0 else c) =
        ∑ word : Fin M → Bool, if word v = word w then c else 0 := by
    rw [← e.sum_comp]
    apply Finset.sum_congr rfl
    intro word _
    change (if flipAt word v = flipAt word w then 0 else c) = _
    have hvw' : w ≠ v := Ne.symm hvw
    simp only [flipAt]
    simp [hvw']
    cases word v <;> cases word w <;> simp
  have htotal :
      (∑ word : Fin M → Bool, if word v = word w then 0 else c) +
          (∑ word : Fin M → Bool, if word v = word w then c else 0) = 1 := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ word : Fin M → Bool,
          ((if word v = word w then 0 else c) +
            (if word v = word w then c else 0))) =
          ∑ _word : Fin M → Bool, c := by
            apply Finset.sum_congr rfl
            intro word _
            by_cases h : word v = word w <;> simp [h]
      _ = (Fintype.card (Fin M → Bool) : ℝ) * c := by simp
      _ = 1 := by
        rw [Fintype.card_fun]
        simp only [Fintype.card_fin, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
        dsimp [c]
        exact mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))
  change (∑ word : Fin M → Bool, if word v = word w then 0 else c) = 2⁻¹
  rw [hswap] at htotal
  linarith

private lemma fairWordLaw_agreement_mean {M : Nat} (v w : Fin M) (hvw : v ≠ w) :
    ∫ word, (if word v = word w then 1 else 0 : ℝ) ∂fairWordLaw M = 1 / 2 := by
  letI : IsProbabilityMeasure (fairWordLaw M) :=
    PMF.toMeasure.isProbabilityMeasure (PMF.uniformOfFintype (Fin M → Bool))
  let disagree : (Fin M → Bool) → ℝ :=
    fun word ↦ if word v ≠ word w then 1 else 0
  have hmeas : Measurable disagree := by measurability
  have hint : Integrable disagree (fairWordLaw M) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
    filter_upwards [] with word
    simp only [disagree]
    split_ifs <;> norm_num
  have hpoint : (fun word : Fin M → Bool ↦
      (if word v = word w then 1 else 0 : ℝ)) = fun word ↦ 1 - disagree word := by
    funext word
    by_cases h : word v = word w <;> simp [disagree, h]
  rw [hpoint, integral_sub (integrable_const 1) hint, integral_const,
    fairWordLaw_disagreement_mean v w hvw]
  norm_num

private def streamCode {M d : Nat} (ω : ℕ → (Fin M → Bool)) :
    Fin M → Fin d → Bool := fun v i ↦ ω i.val v

private lemma hammingDistance_streamCode_eq_sum {M d : Nat}
    (ω : ℕ → (Fin M → Bool)) (v w : Fin M) :
    (hammingDistance (streamCode (d := d) ω) v w : ℝ) =
      ∑ i : Fin d, (if ω i.val v ≠ ω i.val w then 1 else 0 : ℝ) := by
  classical
  unfold hammingDistance
  rw [Finset.cast_card, Finset.sum_filter]
  simp only [Finset.mem_univ, if_true, streamCode]
  rfl

private lemma streamCode_bad_pair_measure {M d : Nat} (hd : 0 < d)
    (v w : Fin M) (hvw : v ≠ w) :
    (Measure.infinitePi (fun _ : ℕ ↦ fairWordLaw M)).real
        {ω | (hammingDistance (streamCode (d := d) ω) v w : ℝ) < (d : ℝ) / 4} ≤
      Real.exp (-(d : ℝ) / 8) := by
  letI : IsProbabilityMeasure (fairWordLaw M) :=
    PMF.toMeasure.isProbabilityMeasure (PMF.uniformOfFintype (Fin M → Bool))
  letI : ∀ _i : ℕ, IsProbabilityMeasure (fairWordLaw M) := fun _ ↦ inferInstance
  letI : IsProbabilityMeasure
      (Measure.infinitePi (fun _ : ℕ ↦ fairWordLaw M)) := inferInstance
  let agree : (Fin M → Bool) → ℝ :=
    fun word ↦ if word v = word w then 1 else 0
  have hagree_meas : Measurable agree := by measurability
  have hagree_bound : ∀ word, agree word ∈ Set.Icc (0 : ℝ) 1 := by
    intro word
    simp only [agree]
    split_ifs <;> norm_num
  have htail := Causalean.Stat.Concentration.hoeffding_ge
    (fairWordSample M) hagree_meas (a := 0) (b := 1) (by norm_num)
    (ae_of_all _ hagree_bound) d hd (ε := 1 / 4) (by norm_num)
  rw [fairWordLaw_agreement_mean v w hvw] at htail
  calc
    (Measure.infinitePi (fun _ : ℕ ↦ fairWordLaw M)).real
        {ω | (hammingDistance (streamCode (d := d) ω) v w : ℝ) < (d : ℝ) / 4} ≤
        (Measure.infinitePi (fun _ : ℕ ↦ fairWordLaw M)).real
          {ω | (1 / 4 : ℝ) ≤
            (fairWordSample M).sampleMean agree d ω - 1 / 2} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro ω hω
      change (1 / 4 : ℝ) ≤
        (d : ℝ)⁻¹ * ∑ i ∈ Finset.range d, agree (ω i) - 1 / 2
      rw [← Fin.sum_univ_eq_sum_range]
      have hpartition :
          (hammingDistance (streamCode (d := d) ω) v w : ℝ) +
              ∑ i : Fin d, agree (ω i.val) = d := by
        rw [hammingDistance_streamCode_eq_sum]
        rw [← Finset.sum_add_distrib]
        calc
          (∑ i : Fin d,
              ((if ω i.val v ≠ ω i.val w then 1 else 0 : ℝ) + agree (ω i.val))) =
              ∑ _i : Fin d, (1 : ℝ) := by
                apply Finset.sum_congr rfl
                intro i _
                by_cases h : ω i.val v = ω i.val w <;> simp [agree, h]
          _ = d := by simp
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd
      change (hammingDistance (streamCode (d := d) ω) v w : ℝ) < (d : ℝ) / 4 at hω
      have hagree : 3 * (d : ℝ) / 4 < ∑ i : Fin d, agree (ω i.val) := by
        linarith
      have hscaled : (3 / 4 : ℝ) <
          (d : ℝ)⁻¹ * ∑ i : Fin d, agree (ω i.val) := by
        rw [inv_mul_eq_div]
        exact (lt_div_iff₀ hdR).2 (by nlinarith)
      linarith
    _ ≤ Real.exp (-2 * d * (1 / 4 : ℝ) ^ 2 / (1 - 0) ^ 2) := htail
    _ = Real.exp (-(d : ℝ) / 8) := by congr 1 <;> ring

/-- At the logarithmic code length, there are `M` binary words whose pairwise Hamming distances
are at least one quarter of the length. For [the candidate-policy count](hyp:M) and
[the candidate-policy count assumption](hyp:hM), this establishes
[the code separated exists result](goal). -/
-- @node: codeSeparated_exists
lemma codeSeparated_exists (M : Nat) (hM : 2 ≤ M) :
    ∃ code : Fin M → Fin (codeDimension M) → Bool, CodeSeparated code := by
  classical
  let μ : Measure (ℕ → (Fin M → Bool)) :=
    Measure.infinitePi (fun _ : ℕ ↦ fairWordLaw M)
  let bad : (Fin M × Fin M) → Set (ℕ → (Fin M → Bool)) := fun p ↦
    if p.1 ≠ p.2 then
      {ω | (hammingDistance (streamCode (d := codeDimension M) ω) p.1 p.2 : ℝ) <
        (codeDimension M : ℝ) / 4}
    else ∅
  have hbad (p : Fin M × Fin M) :
      μ.real (bad p) ≤ Real.exp (-(codeDimension M : ℝ) / 8) := by
    by_cases hp : p.1 ≠ p.2
    · simpa [μ, bad, hp] using
        streamCode_bad_pair_measure (codeDimension_pos M hM) p.1 p.2 hp
    · dsimp only [bad]
      rw [if_neg hp]
      rw [measureReal_empty]
      exact (Real.exp_pos _).le
  have hunion : μ.real (⋃ p, bad p) ≤ 1 / M := by
    calc
      μ.real (⋃ p, bad p) ≤ ∑ p : Fin M × Fin M, μ.real (bad p) :=
        measureReal_iUnion_fintype_le bad
      _ ≤ ∑ _p : Fin M × Fin M,
          Real.exp (-(codeDimension M : ℝ) / 8) := by
            apply Finset.sum_le_sum
            intro p _
            exact hbad p
      _ = (M : ℝ) ^ 2 * Real.exp (-(codeDimension M : ℝ) / 8) := by
        simp [Fintype.card_prod]
        ring
      _ ≤ 1 / M := codeDimension_pair_union_bound M hM
  have hlt : μ.real (⋃ p, bad p) < 1 := by
    have hMR : (1 : ℝ) < M := by exact_mod_cast hM
    exact hunion.trans_lt (by
      simpa using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hMR)
  have hgood : ∃ ω : ℕ → (Fin M → Bool), ω ∉ ⋃ p, bad p := by
    by_contra h
    push_neg at h
    have huniv : (⋃ p, bad p) = Set.univ := Set.eq_univ_of_forall h
    haveI : IsProbabilityMeasure (fairWordLaw M) :=
      PMF.toMeasure.isProbabilityMeasure (PMF.uniformOfFintype (Fin M → Bool))
    haveI : ∀ _i : ℕ, IsProbabilityMeasure (fairWordLaw M) := fun _ ↦ inferInstance
    haveI : IsProbabilityMeasure μ := by
      dsimp [μ]
      infer_instance
    rw [huniv, probReal_univ] at hlt
    exact (lt_irrefl 1 hlt)
  obtain ⟨ω, hω⟩ := hgood
  refine ⟨streamCode (d := codeDimension M) ω, ?_, ?_⟩
  · intro v w heq
    by_contra hvw
    have hsep : (codeDimension M : ℝ) / 4 ≤
        hammingDistance (streamCode (d := codeDimension M) ω) v w := by
      by_contra hdist
      have hmem : ω ∈ bad (v, w) := by
        dsimp only [bad]
        rw [if_pos hvw]
        exact lt_of_not_ge hdist
      exact hω (Set.mem_iUnion.2 ⟨(v, w), hmem⟩)
    have hzero : hammingDistance (streamCode (d := codeDimension M) ω) v w = 0 := by
      unfold hammingDistance
      apply Finset.card_eq_zero.mpr
      simp only [Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
      intro i
      intro hne
      exact hne (congrFun heq i)
    have hdR : (0 : ℝ) < codeDimension M := by
      exact_mod_cast codeDimension_pos M hM
    rw [hzero, Nat.cast_zero] at hsep
    linarith
  · intro v w hvw
    by_contra hdist
    have hmem : ω ∈ bad (v, w) := by
      dsimp only [bad]
      rw [if_pos hvw]
      exact lt_of_not_ge hdist
    exact hω (Set.mem_iUnion.2 ⟨(v, w), hmem⟩)

end CausalSmith.Stat.PomdpPolicyclassRegret
