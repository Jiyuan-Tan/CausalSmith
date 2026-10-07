module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.RatioMean
public import Mathlib.MeasureTheory.Integral.Pi

/-! Second moments for the zero-safe marked Poisson ratio branch. -/

public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean

attribute [local instance] markedObsLaw_isProbabilityMeasure
attribute [local instance] Classical.propDecidable

private def ratioPattern {X : Type*} {n : ℕ} (B : Set X)
    (U : Finset (Fin n)) : Set (Fin n → X) :=
  Set.univ.pi (fun i ↦ if i ∈ U then B else Bᶜ)

private lemma measurable_ratioPattern {X : Type*} [MeasurableSpace X]
    {n : ℕ} {B : Set X} (hB : MeasurableSet B) (U : Finset (Fin n)) :
    MeasurableSet (ratioPattern B U) := by
  classical
  apply (measurableSet_pi Set.countable_univ).mpr
  left
  intro i hi
  split_ifs
  · exact hB
  · exact hB.compl

private lemma iidEventCount_eq_card {X : Type*} {n : ℕ}
    (A : Set X) (x : Fin n → X) :
    iidEventCount A x = ((Finset.univ.filter (fun i ↦ x i ∈ A)).card : ℝ) := by
  classical
  exact Finset.sum_boole _ _

private lemma mem_ratioPattern_iff {X : Type*} {n : ℕ} (B : Set X)
    (U : Finset (Fin n)) (x : Fin n → X) :
    x ∈ ratioPattern B U ↔
      Finset.univ.filter (fun i ↦ x i ∈ B) = U := by
  classical
  simp only [ratioPattern, Set.mem_univ_pi]
  constructor
  · intro hx
    ext i
    by_cases hi : i ∈ U
    · have h := hx i
      simpa [hi] using h
    · have h := hx i
      simp only [hi, if_false, Set.mem_compl_iff] at h
      simp [hi, h]
  · intro hx i
    have hi : x i ∈ B ↔ i ∈ U := by
      have := Finset.ext_iff.mp hx i
      simpa using this
    by_cases h : i ∈ U
    · simpa [h] using hi.mpr h
    · simpa [h] using hi.not.mpr h

/-- On a rectangle fixing exactly the observations in `B`, the squared
centered smaller-event count has its binomial variance bound.  The statement
is division free, so it also covers zero pattern mass. -/
private lemma iid_nested_pattern_centered_sq_le
    {X : Type*} [MeasurableSpace X] [Fintype X] [MeasurableSingletonClass X]
    (P : Measure X) [IsProbabilityMeasure P]
    {n : ℕ} (U : Finset (Fin n)) {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) :
    (∫ x : Fin n → X,
        (P.real B * iidEventCount A x - P.real A * (U.card : ℝ)) ^ 2
      ∂(Measure.pi (fun _ : Fin n ↦ P)).restrict (ratioPattern B U)) ≤
      (U.card : ℝ) * (P.real B) ^ 2 *
        (Measure.pi (fun _ : Fin n ↦ P)).real (ratioPattern B U) := by
  classical
  let S : Fin n → Set X := fun i ↦ if i ∈ U then B else Bᶜ
  let μ : Measure (Fin n → X) := Measure.pi (fun i ↦ P.restrict (S i))
  letI (i : Fin n) : IsFiniteMeasure (P.restrict (S i)) := inferInstance
  letI : IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance
  let q : Fin n → ℝ := fun i ↦ P.real (S i)
  let ζ : Fin n → X → ℝ := fun i y ↦
    if i ∈ U then P.real B * (if y ∈ A then 1 else 0) - P.real A else 0
  have hrestrict :
      (Measure.pi (fun _ : Fin n ↦ P)).restrict (ratioPattern B U) = μ := by
    simpa [ratioPattern, S, μ] using
      (Measure.restrict_pi_pi (fun _ : Fin n ↦ P) S)
  have hmass : (Measure.pi (fun _ : Fin n ↦ P)).real (ratioPattern B U) =
      ∏ i, q i := by
    rw [← measureReal_restrict_apply_univ, hrestrict]
    have h := integral_fintype_prod_eq_prod
      (μ := fun i ↦ P.restrict (S i)) (fun _ _ ↦ (1 : ℝ))
    rw [← measureReal_restrict_apply_univ]
    simpa [μ, q, integral_const, measureReal_restrict_apply_univ] using h
  have hcount (x : Fin n → X) (hx : x ∈ ratioPattern B U) :
      P.real B * iidEventCount A x - P.real A * (U.card : ℝ) =
        ∑ i, ζ i (x i) := by
    have hout (i : Fin n) (hi : i ∉ U) : x i ∉ A := by
      have hiB : x i ∉ B := by
        have := (show ∀ i, x i ∈ S i by simpa [ratioPattern, S] using hx) i
        simpa [S, hi] using this
      exact fun hiA ↦ hiB (hAB hiA)
    unfold iidEventCount
    rw [Finset.mul_sum]
    rw [show P.real A * (U.card : ℝ) =
        ∑ i : Fin n, P.real A * (if i ∈ U then 1 else 0) by
          simp [mul_comm]]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hiU : i ∈ U
    · simp [ζ, hiU]
    · simp [ζ, hiU, hout i hiU]
  have hζzero (i : Fin n) : ∫ y, ζ i y ∂P.restrict (S i) = 0 := by
    by_cases hi : i ∈ U
    · have heq : (fun y : X ↦ ζ i y) =
          fun y ↦ P.real B * A.indicator (fun _ ↦ (1 : ℝ)) y - P.real A := by
        funext y
        simp [ζ, hi, Set.indicator_apply]
      rw [heq, integral_sub, integral_const_mul, integral_indicator_const 1 hA,
        measureReal_restrict_apply hA, integral_const]
      · simp [S, hi, Set.inter_eq_left.mpr hAB]
      · exact Integrable.of_finite
      · exact Integrable.of_finite
    · simp [ζ, hi]
  have hζsq (i : Fin n) :
      ∫ y, (ζ i y) ^ 2 ∂P.restrict (S i) ≤
        if i ∈ U then (P.real B) ^ 2 * q i else 0 := by
    by_cases hi : i ∈ U
    · have hpoint (y : X) : (ζ i y) ^ 2 ≤ (P.real B) ^ 2 := by
        by_cases hy : y ∈ A
        · have hmono : P.real A ≤ P.real B := measureReal_mono hAB
          simp [ζ, hi, hy]
          nlinarith [measureReal_nonneg (μ := P) (s := A),
            measureReal_nonneg (μ := P) (s := B)]
        · simp [ζ, hi, hy]
          nlinarith [measureReal_nonneg (μ := P) (s := A),
            measureReal_nonneg (μ := P) (s := B), measureReal_mono (μ := P) hAB]
      rw [if_pos hi]
      calc
        _ ≤ ∫ _y, (P.real B) ^ 2 ∂P.restrict (S i) := by
          exact integral_mono Integrable.of_finite Integrable.of_finite hpoint
        _ = _ := by simp [q, measureReal_restrict_apply_univ, mul_comm]
    · simp [ζ, hi]
  have hfun : (∫ x : Fin n → X,
      (P.real B * iidEventCount A x - P.real A * (U.card : ℝ)) ^ 2
        ∂(Measure.pi (fun _ : Fin n ↦ P)).restrict (ratioPattern B U)) =
      ∫ x : Fin n → X, (∑ i, ζ i (x i)) ^ 2
        ∂(Measure.pi (fun _ : Fin n ↦ P)).restrict (ratioPattern B U) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurable_ratioPattern hB U)] with x hx
    apply congrArg (fun z : ℝ ↦ z ^ 2)
    exact hcount x hx
  rw [hfun, hrestrict]
  -- Expand the square.  Off-diagonal coordinate integrals vanish; diagonal
  -- terms are bounded by the containing-event mass squared.
  rw [show (fun x : Fin n → X ↦ (∑ i, ζ i (x i)) ^ 2) =
      fun x ↦ ∑ i, ∑ j, ζ i (x i) * ζ j (x j) by
    funext x
    simp only [sq, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]]
  rw [integral_finsetSum]
  · calc
      ∑ i, ∫ x, ∑ j, ζ i (x i) * ζ j (x j) ∂μ ≤
          ∑ i : Fin n, if i ∈ U then
            (P.real B) ^ 2 * ∏ j, q j else 0 := by
        apply Finset.sum_le_sum
        intro i hi
        rw [integral_finsetSum]
        · exact (show
        ∑ j, ∫ x, ζ i (x i) * ζ j (x j) ∂μ ≤
            if i ∈ U then (P.real B) ^ 2 * ∏ j, q j else 0 by
          rw [Finset.sum_eq_single i]
          · have hprod := integral_fintype_prod_eq_prod
                (μ := fun k ↦ P.restrict (S k))
                (fun k y ↦ if k = i then (ζ i y) ^ 2 else 1)
            rw [show (∫ x, ζ i (x i) * ζ i (x i) ∂μ) =
                ∫ x, ∏ k, (if k = i then (ζ i (x k)) ^ 2 else 1)
                  ∂Measure.pi (fun k ↦ P.restrict (S k)) by
              congr 1
              funext x
              simp [μ, sq]]
            rw [hprod]
            have hrest :
                (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i,
                    ∫ y, (if k = i then (ζ i y) ^ 2 else 1)
                      ∂P.restrict (S k)) =
                  ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, q k := by
              apply Finset.prod_congr rfl
              intro k hk
              have hki : k ≠ i := (Finset.mem_erase.mp hk).1
              simp [hki, q, integral_const, measureReal_restrict_apply_univ]
            by_cases hi : i ∈ U
            · rw [if_pos hi, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
              rw [hrest]
              simp only [if_true]
              have hqprod : q i *
                  ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, q k = ∏ j, q j :=
                Finset.mul_prod_erase _ _ (Finset.mem_univ i)
              rw [← hqprod]
              have hs := hζsq i
              rw [if_pos hi] at hs
              simpa [mul_assoc] using mul_le_mul_of_nonneg_right hs
                (Finset.prod_nonneg fun j _ ↦ measureReal_nonneg)
            · rw [if_neg hi, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
              rw [hrest]
              simp only [if_true]
              simp [hi, ζ]
          · intro j hj hji
            have hprod := integral_fintype_prod_eq_prod
              (μ := fun k ↦ P.restrict (S k))
              (fun k y ↦ if k = i then ζ i y else if k = j then ζ j y else 1)
            rw [show (∫ x, ζ i (x i) * ζ j (x j) ∂μ) =
                ∫ x, ∏ k, (if k = i then ζ i (x k)
                    else if k = j then ζ j (x k) else 1)
                  ∂Measure.pi (fun k ↦ P.restrict (S k)) by
              congr 1
              funext x
              change ζ i (x i) * ζ j (x j) =
                ∏ k, (if k = i then ζ i (x k)
                  else if k = j then ζ j (x k) else 1)
              let f : Fin n → ℝ := fun k ↦
                if k = i then ζ i (x k) else if k = j then ζ j (x k) else 1
              change ζ i (x i) * ζ j (x j) = ∏ k, f k
              rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
              have hjmem : j ∈ (Finset.univ : Finset (Fin n)).erase i := by
                exact Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
              rw [← Finset.mul_prod_erase _ _ hjmem]
              have hrestone : ∏ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j,
                  f k = 1 := by
                apply Finset.prod_eq_one
                intro k hk
                have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
                have hki : k ≠ i := (Finset.mem_erase.mp
                  (Finset.mem_erase.mp hk).2).1
                simp [f, hki, hkj]
              rw [hrestone]
              simp [f, hji, Ne.symm hji]]
            rw [hprod]
            rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
            rw [show (∫ y, (if i = i then ζ i y else if i = j then ζ j y else 1)
                ∂P.restrict (S i)) = 0 by simpa using hζzero i]
            simp
          · simp)
        · intro j hj
          exact Integrable.of_finite
      _ = (U.card : ℝ) * (P.real B) ^ 2 *
          (Measure.pi (fun _ : Fin n ↦ P)).real (ratioPattern B U) := by
        simp [hmass, mul_assoc]
  · intro i hi
    exact integrable_finsetSum Finset.univ fun j hj ↦ Integrable.of_finite

private lemma disjoint_ratioPatterns {X : Type*} {n : ℕ} (B : Set X)
    (U V : Finset (Fin n)) (hUV : U ≠ V) :
    Disjoint (ratioPattern B U) (ratioPattern B V) := by
  classical
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hUV ((mem_ratioPattern_iff B U x).mp hx |>.symm.trans
    ((mem_ratioPattern_iff B V x).mp hy))

/-- Given [the specified inputs and assumptions](hyp:X,P,n,k,hk,A,B,hA,hB,hAB,hPB), [the stated mathematical conclusion holds](goal). -/
lemma iid_successFraction_count_fibre_centered_sq_le
    {X : Type*} [MeasurableSpace X] [Fintype X] [MeasurableSingletonClass X]
    (P : Measure X) [IsProbabilityMeasure P] (n k : ℕ) (hk : 0 < k)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B) (hPB : 0 < P.real B) :
    (∫ x : Fin n → X,
        (successFraction A B (fixedSizeEmbed n x) - P.real A / P.real B) ^ 2
      ∂(Measure.pi (fun _ : Fin n ↦ P)).restrict
        {x | iidEventCount B x = (k : ℝ)}) ≤
      (k : ℝ)⁻¹ *
        (Measure.pi (fun _ : Fin n ↦ P)).real
          {x | iidEventCount B x = (k : ℝ)} := by
  classical
  let T := Finset.univ.filter (fun U : Finset (Fin n) ↦ U.card = k)
  let R := fun U : Finset (Fin n) ↦ ratioPattern B U
  have hset : {x : Fin n → X | iidEventCount B x = (k : ℝ)} =
      ⋃ U ∈ T, R U := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hx
      let U := Finset.univ.filter (fun i ↦ x i ∈ B)
      refine ⟨U, ?_, ?_⟩
      · simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        exact_mod_cast (iidEventCount_eq_card B x).symm.trans hx
      · exact (mem_ratioPattern_iff B U x).mpr rfl
    · rintro ⟨U, hU, hx⟩
      have hcard : U.card = k := (Finset.mem_filter.mp hU).2
      rw [iidEventCount_eq_card B x, (mem_ratioPattern_iff B U x).mp hx, hcard]
  have hm : ∀ U ∈ T, MeasurableSet (R U) :=
    fun U _ ↦ measurable_ratioPattern hB U
  have hd : Set.PairwiseDisjoint (↑T) R :=
    fun U _ V _ hUV ↦ disjoint_ratioPatterns B U V hUV
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hPBR : P.real B ≠ 0 := ne_of_gt hPB
  let f : (Fin n → X) → ℝ := fun x ↦
    (successFraction A B (fixedSizeEmbed n x) - P.real A / P.real B) ^ 2
  have hf : Integrable f (Measure.pi (fun _ : Fin n ↦ P)) := by
    apply Integrable.of_bound
      (((measurable_successFraction hA hB).comp
        (measurable_fixedSizeEmbed n) |>.sub measurable_const).pow_const 2).aestronglyMeasurable 1
    filter_upwards [] with x
    rcases successFraction_bounds hAB (fixedSizeEmbed n x) with ⟨hs0, hs1⟩
    have hp0 : 0 ≤ P.real A / P.real B := div_nonneg measureReal_nonneg hPB.le
    have hp1 : P.real A / P.real B ≤ 1 := (div_le_one hPB).2 (measureReal_mono hAB)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (successFraction A B (fixedSizeEmbed n x) - P.real A / P.real B) ^ 2 ≤ 1
    nlinarith
  rw [hset, integral_biUnion_finset T hm hd (fun _ _ ↦ hf.integrableOn),
    measureReal_biUnion_finset hd hm]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro U hU
  have hcard : U.card = k := (Finset.mem_filter.mp hU).2
  have heq : f =ᵐ[(Measure.pi (fun _ : Fin n ↦ P)).restrict (R U)]
      fun x ↦
        (P.real B * iidEventCount A x - P.real A * (k : ℝ)) ^ 2 /
          ((P.real B) ^ 2 * (k : ℝ) ^ 2) := by
    filter_upwards [ae_restrict_mem (hm U hU)] with x hx
    have hxB : iidEventCount B x = (k : ℝ) := by
      rw [iidEventCount_eq_card B x, (mem_ratioPattern_iff B U x).mp hx, hcard]
    simp only [f, successFraction, eventCount_fixedSizeEmbed, hxB, hkR, if_false]
    field_simp
  rw [integral_congr_ae heq, integral_div]
  have hpat := iid_nested_pattern_centered_sq_le P U hA hB hAB
  rw [hcard] at hpat
  apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hPB) (sq_pos_of_pos (by exact_mod_cast hk)))).2
  calc
    (∫ x, (P.real B * iidEventCount A x - P.real A * (k : ℝ)) ^ 2
        ∂(Measure.pi (fun _ : Fin n ↦ P)).restrict (R U)) ≤
        (k : ℝ) * (P.real B) ^ 2 *
          (Measure.pi (fun _ : Fin n ↦ P)).real (R U) := hpat
    _ = ((k : ℝ)⁻¹ * (Measure.pi (fun _ : Fin n ↦ P)).real (R U)) *
        ((P.real B) ^ 2 * (k : ℝ) ^ 2) := by field_simp

/-- Given [the specified inputs and assumptions](hyp:X,P,n,A,B,hA,hB,hAB,hPB), [the stated mathematical conclusion holds](goal). -/
lemma iid_successFraction_centered_sq_le_inverseCount
    {X : Type*} [MeasurableSpace X] [Fintype X] [MeasurableSingletonClass X]
    (P : Measure X) [IsProbabilityMeasure P] (n : ℕ)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B) (hPB : 0 < P.real B) :
    (∫ x : Fin n → X,
      (successFraction A B (fixedSizeEmbed n x) - P.real A / P.real B) ^ 2
        ∂Measure.pi (fun _ : Fin n ↦ P)) ≤
      ∫ x : Fin n → X,
        (if 0 < iidEventCount B x then (iidEventCount B x)⁻¹ else 1)
          ∂Measure.pi (fun _ : Fin n ↦ P) := by
  classical
  let μ : Measure (Fin n → X) := Measure.pi (fun _ : Fin n ↦ P)
  let F : ℕ → Set (Fin n → X) := fun k ↦ {x | iidEventCount B x = (k : ℝ)}
  let T := Finset.range (n + 1)
  let f : (Fin n → X) → ℝ := fun x ↦
    (successFraction A B (fixedSizeEmbed n x) - P.real A / P.real B) ^ 2
  let g : (Fin n → X) → ℝ := fun x ↦
    if 0 < iidEventCount B x then (iidEventCount B x)⁻¹ else 1
  have hm : ∀ k ∈ T, MeasurableSet (F k) := fun k _ ↦
    (measurable_iidEventCount hB n) (measurableSet_singleton _)
  have hd : Set.PairwiseDisjoint (↑T) F := by
    intro k _ l _ hkl
    apply Set.disjoint_left.mpr
    intro x hx hy
    apply hkl
    exact_mod_cast (hx.symm.trans hy : (k : ℝ) = (l : ℝ))
  have hcover : (⋃ k ∈ T, F k) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    let U := Finset.univ.filter (fun i : Fin n ↦ x i ∈ B)
    have hU : U.card ≤ n :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
    exact Set.mem_iUnion.mpr ⟨U.card, Set.mem_iUnion.mpr
      ⟨Finset.mem_range.mpr (by omega), iidEventCount_eq_card B x⟩⟩
  have hf : Integrable f μ := Integrable.of_finite
  have hg : Integrable g μ := Integrable.of_finite
  change (∫ x, f x ∂μ) ≤ ∫ x, g x ∂μ
  rw [← Measure.restrict_univ (μ := μ), ← hcover,
    integral_biUnion_finset T hm hd (fun _ _ ↦ hf.integrableOn),
    integral_biUnion_finset T hm hd (fun _ _ ↦ hg.integrableOn)]
  apply Finset.sum_le_sum
  intro k hkT
  by_cases hk0 : k = 0
  · subst k
    have hpoint : ∀ x ∈ F 0, f x ≤ g x := by
      intro x hx
      have hp0 : 0 ≤ P.real A / P.real B := div_nonneg measureReal_nonneg hPB.le
      have hp1 : P.real A / P.real B ≤ 1 := (div_le_one hPB).2 (measureReal_mono hAB)
      have hx0 : iidEventCount B x = 0 := by simpa [F] using hx
      have hs0 : successFraction A B (fixedSizeEmbed n x) = 0 := by
        simp [successFraction, eventCount_fixedSizeEmbed, hx0]
      simp only [f, g, hs0, hx0, lt_self_iff_false, if_false, zero_sub]
      nlinarith
    apply integral_mono_ae hf.restrict hg.restrict
    filter_upwards [ae_restrict_mem (hm 0 hkT)] with x hx
    exact hpoint x hx
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hleft := iid_successFraction_count_fibre_centered_sq_le
      P n k hkpos hA hB hAB hPB
    have hright : (∫ x, g x ∂μ.restrict (F k)) =
        (k : ℝ)⁻¹ * μ.real (F k) := by
      have heq : g =ᵐ[μ.restrict (F k)] (fun _ ↦ (k : ℝ)⁻¹) := by
        filter_upwards [ae_restrict_mem (hm k hkT)] with x hx
        have hxk : iidEventCount B x = (k : ℝ) := by simpa [F] using hx
        simp [g, hxk, hkpos]
      rw [integral_congr_ae heq, integral_const]
      rw [measureReal_restrict_apply_univ]
      simp [smul_eq_mul, mul_comm]
    change (∫ x, f x ∂μ.restrict (F k)) ≤ _
    rw [hright]
    exact hleft

/-- Given [the specified inputs and assumptions](hyp:lambda), [the stated mathematical conclusion holds](goal). -/
lemma poisson_zeroSafeInverse_expectation_le (lambda : ℝ≥0) :
    (∫ k : ℕ, (if 0 < k then ((k : ℝ)⁻¹) else 1)
      ∂poissonMeasure lambda) ≤ 4 / (1 + (lambda : ℝ)) := by
  let g : ℕ → ℝ := fun k ↦ if 0 < k then ((k : ℝ)⁻¹) else 1
  have hg : Integrable g (poissonMeasure lambda) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    filter_upwards with k
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · by_cases hk : 0 < k
      · simp only [g, hk, if_true]
        apply (inv_le_one₀ (by positivity : 0 < (k : ℝ))).2
        exact_mod_cast hk
      · simp [g, hk]
    · simp only [g]
      split_ifs
      · positivity
      · positivity
  by_cases hlambda : (lambda : ℝ) ≤ 1
  · calc
      (∫ k : ℕ, (if 0 < k then ((k : ℝ)⁻¹) else 1)
          ∂poissonMeasure lambda) = ∫ k, g k ∂poissonMeasure lambda := rfl
      _ ≤ ∫ _k : ℕ, (1 : ℝ) ∂poissonMeasure lambda := by
        apply integral_mono hg (integrable_const 1)
        intro k
        by_cases hk : 0 < k
        · simp only [g, hk, if_true]
          apply (inv_le_one₀ (by positivity : 0 < (k : ℝ))).2
          exact_mod_cast hk
        · simp [g, hk]
      _ = 1 := by simp
      _ ≤ 4 / (1 + (lambda : ℝ)) := by
        apply (le_div_iff₀ (by positivity : 0 < 1 + (lambda : ℝ))).2
        linarith
  · have hlambda_pos : 0 < (lambda : ℝ) := by
      have : 1 < (lambda : ℝ) := lt_of_not_ge hlambda
      linarith
    let r : ℕ → ℝ := fun k ↦ (((k + 1 : ℕ) : ℝ))⁻¹
    have hr : Integrable r (poissonMeasure lambda) :=
      (Causalean.Mathlib.Probability.Poisson.shifted_reciprocal_memLp_two lambda).integrable
        (by norm_num)
    have hpoint (k : ℕ) : g k ≤ 2 * r k := by
      by_cases hk : k = 0
      · subst k
        simp [g, r]
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        simp only [g, hkpos, if_true, r]
        rw [← one_div, show 2 * (((k + 1 : ℕ) : ℝ))⁻¹ =
          2 / (((k + 1 : ℕ) : ℝ)) by rw [div_eq_mul_inv]]
        apply (div_le_div_iff₀ (by positivity : 0 < (k : ℝ))
          (by positivity : 0 < ((k + 1 : ℕ) : ℝ))).2
        norm_num
        exact_mod_cast (show k + 1 ≤ 2 * k by omega)
    have hshift :=
      Causalean.Mathlib.Probability.Poisson.shifted_reciprocal_first_moment lambda
    have hr_eq : (∫ k : ℕ, r k ∂poissonMeasure lambda) =
        (1 - Real.exp (-(lambda : ℝ))) / (lambda : ℝ) := by
      apply (eq_div_iff hlambda_pos.ne').2
      simpa [r, mul_comm] using hshift
    calc
      (∫ k : ℕ, (if 0 < k then ((k : ℝ)⁻¹) else 1)
          ∂poissonMeasure lambda) = ∫ k, g k ∂poissonMeasure lambda := rfl
      _ ≤ ∫ k, 2 * r k ∂poissonMeasure lambda := by
        exact integral_mono hg (hr.const_mul 2) hpoint
      _ = 2 * ((1 - Real.exp (-(lambda : ℝ))) / (lambda : ℝ)) := by
        rw [integral_const_mul, hr_eq]
      _ ≤ 2 / (lambda : ℝ) := by
        have hexp : 0 ≤ Real.exp (-(lambda : ℝ)) := (Real.exp_pos _).le
        rw [← mul_div_assoc]
        apply div_le_div_of_nonneg_right _ hlambda_pos.le
        linarith
      _ ≤ 4 / (1 + (lambda : ℝ)) := by
        apply (div_le_div_iff₀ hlambda_pos (by positivity : 0 < 1 + (lambda : ℝ))).2
        have : 1 ≤ (lambda : ℝ) := le_of_not_ge hlambda
        nlinarith

/-- Given [the specified inputs and assumptions](hyp:X,P,lambda,A,B,hA,hB,hAB,hPB), [the stated mathematical conclusion holds](goal). -/
lemma finitePoisson_successFraction_centered_sq_le
    {X : Type*} [MeasurableSpace X] [Fintype X] [MeasurableSingletonClass X]
    [DecidableEq X] (P : Measure X) [IsProbabilityMeasure P]
    (lambda : ℝ≥0) {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B) (hPB : 0 < P.real B) :
    (∫ s : FiniteSample X,
      (successFraction A B s - P.real A / P.real B) ^ 2
        ∂finitePoissonSampleLaw P lambda) ≤
      4 / (1 + (lambda : ℝ) * P.real B) := by
  classical
  let target : ℝ := P.real A / P.real B
  let f : FiniteSample X → ℝ := fun s ↦ (successFraction A B s - target) ^ 2
  let g : FiniteSample X → ℝ := fun s ↦
    if 0 < Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment.eventCount s B
      then ((Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment.eventCount s B : ℝ))⁻¹
      else 1
  have hf : Measurable f := by
    exact ((measurable_successFraction hA hB).sub measurable_const).pow_const 2
  have hg : Measurable g := by
    have hh : Measurable (fun k : ℕ ↦ if 0 < k then ((k : ℝ)⁻¹) else 1) :=
      measurable_of_countable _
    exact hh.comp
      (Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment.measurable_eventCount B hB)
  have hfb (s : FiniteSample X) : ‖f s‖ ≤ 1 := by
    rcases successFraction_bounds hAB s with ⟨hs0, hs1⟩
    have ht0 : 0 ≤ target := div_nonneg measureReal_nonneg hPB.le
    have ht1 : target ≤ 1 := (div_le_one hPB).2 (measureReal_mono hAB)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    dsimp [f]
    nlinarith
  have hgb (s : FiniteSample X) : ‖g s‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · by_cases hk : 0 <
      Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment.eventCount s B
      · simp only [g, hk, if_true]
        apply (inv_le_one₀ (by exact_mod_cast hk : (0 : ℝ) < _)).2
        exact_mod_cast hk
      · simp [g, hk]
    · simp only [g]
      split_ifs <;> positivity
  rw [show (fun s : FiniteSample X ↦
      (successFraction A B s - P.real A / P.real B) ^ 2) = f by rfl]
  rw [integral_finitePoissonSampleLaw_eq_integral_iid P lambda f hf 1 hfb]
  calc
    (∫ n : ℕ, ∫ x : Fin n → X, f (fixedSizeEmbed n x)
        ∂Measure.pi (fun _ : Fin n ↦ P) ∂poissonMeasure lambda) ≤
        ∫ n : ℕ, ∫ x : Fin n → X, g (fixedSizeEmbed n x)
          ∂Measure.pi (fun _ : Fin n ↦ P) ∂poissonMeasure lambda := by
      apply integral_mono
      · exact Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
          (Filter.Eventually.of_forall fun n ↦ by
            simpa using norm_integral_le_of_norm_le_const
              (μ := Measure.pi (fun _ : Fin n ↦ P))
              (f := fun x : Fin n → X ↦ f (fixedSizeEmbed n x))
              (Filter.Eventually.of_forall fun x ↦ hfb _))
      · exact Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
          (Filter.Eventually.of_forall fun n ↦ by
            simpa using norm_integral_le_of_norm_le_const
              (μ := Measure.pi (fun _ : Fin n ↦ P))
              (f := fun x : Fin n → X ↦ g (fixedSizeEmbed n x))
              (Filter.Eventually.of_forall fun x ↦ hgb _))
      · intro n
        calc
          (∫ x : Fin n → X, f (fixedSizeEmbed n x)
              ∂Measure.pi (fun _ : Fin n ↦ P)) ≤
              ∫ x : Fin n → X,
                (if 0 < iidEventCount B x then (iidEventCount B x)⁻¹ else 1)
                ∂Measure.pi (fun _ : Fin n ↦ P) := by
            simpa [f, target] using
              iid_successFraction_centered_sq_le_inverseCount P n hA hB hAB hPB
          _ = ∫ x : Fin n → X, g (fixedSizeEmbed n x)
                ∂Measure.pi (fun _ : Fin n ↦ P) := by
            apply integral_congr_ae
            filter_upwards with x
            have hc := successFraction_eventCount_eq_cast B (fixedSizeEmbed n x)
            rw [Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.eventCount_fixedSizeEmbed]
              at hc
            by_cases hk : 0 <
                Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment.eventCount
                  (fixedSizeEmbed n x) B
            · have hkr : 0 < iidEventCount B x := by
                rw [hc]
                exact_mod_cast hk
              simp [g, hk, hkr, hc]
            · have hk0 :
                Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment.eventCount
                  (fixedSizeEmbed n x) B = 0 := Nat.eq_zero_of_not_pos hk
              have hreal0 : iidEventCount B x = 0 := by simp [hc, hk0]
              simp [g, hk, hreal0]
    _ = ∫ s : FiniteSample X, g s ∂finitePoissonSampleLaw P lambda := by
      rw [integral_finitePoissonSampleLaw_eq_integral_iid P lambda g hg 1 hgb]
    _ = ∫ k : ℕ, (if 0 < k then ((k : ℝ)⁻¹) else 1)
        ∂poissonMeasure (lambda * (P B).toNNReal) := by
      have hmap := finitePoissonSampleLaw_map_eventCount P lambda B hB
      let h : ℕ → ℝ := fun k ↦ if 0 < k then ((k : ℝ)⁻¹) else 1
      have hh : Measurable h := measurable_of_countable _
      rw [← integral_map
        (Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment.measurable_eventCount B hB).aemeasurable
        hh.aestronglyMeasurable, hmap]
    _ ≤ 4 / (1 + ((lambda * (P B).toNNReal : ℝ≥0) : ℝ)) :=
      poisson_zeroSafeInverse_expectation_le _
    _ = 4 / (1 + (lambda : ℝ) * P.real B) := by
      have hmass : ((P B).toNNReal : ℝ) = (P B).toReal := by
        calc
          ((P B).toNNReal : ℝ) =
              (((P B).toNNReal : ℝ≥0∞).toReal) := (ENNReal.coe_toReal _).symm
          _ = (P B).toReal := congrArg ENNReal.toReal
            (ENNReal.coe_toNNReal (measure_ne_top P B))
      simp [NNReal.coe_mul, Measure.real, hmass]

/-- Given [the specified inputs and assumptions](hyp:n,d,P,j,hpos), [the stated mathematical conclusion holds](goal). -/
lemma integral_sq_markedPoissonRatioBranch_sub_cellMean_le
    (n d : ℕ) (P : FullLaw d) (j : Cell d)
    (hpos : 0 < arrivedCell P j) :
    (∫ s, (poissonRatioBranch j s - cellMean P j) ^ 2
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ≤
      4 / (1 + streamSize n * arrivedCell P j) := by
  letI := markedObsLaw_isProbabilityMeasure P
  have h := finitePoisson_successFraction_centered_sq_le
    (markedObsLaw P) ((n : ℝ≥0) / 2)
    (Set.Finite.measurableSet (Set.toFinite (streamEvent 2 j true true)))
    (Set.Finite.measurableSet (Set.toFinite (streamEvent 2 j true false)))
    (streamEvent_ones_subset_arrived 2 j)
    (by rw [markedObsLaw_streamEvent_real, map_obsStreamEvent_arrived_real]; positivity)
  simp_rw [poissonRatioBranch_eq_successFraction]
  rw [cellMean, if_pos hpos]
  rw [markedObsLaw_streamEvent_real, markedObsLaw_streamEvent_real,
    map_obsStreamEvent_arrivedOne_real, map_obsStreamEvent_arrived_real] at h
  have hratio :
      P.1.real {r | inCell r j ∧ r.R = true ∧ r.Y = true} /
          arrivedCell P j =
        (P.1.real {r | inCell r j ∧ r.R = true ∧ r.Y = true} / 3) /
          (arrivedCell P j / 3) := by
    field_simp [ne_of_gt hpos]
  rw [hratio]
  convert h using 1
  unfold streamSize
  push_cast
  ring

end CausalSmith.Stat.MarRareqLogfrontier
