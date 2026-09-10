import Causalean.Stat.Minimax.LeCam
import Causalean.Stat.Minimax.Pinsker
import Causalean.Stat.Minimax.TotalVariation
import Causalean.Mathlib.InformationTheory.ProductKLLeCam
import Causalean.Mathlib.InformationTheory.Fano
import Causalean.Mathlib.InformationTheory.KLBind
import Causalean.Stat.Minimax.ChiSquaredFinite
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-! # Finite-information testing reductions -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace CausalSmith.Stat.BddThicknessEstimabilityFrontier

-- @env: S2
variable {Ω V : Type*} [MeasurableSpace Ω] [MetricSpace V]
  [MeasurableSpace V] [BorelSpace V]

private lemma finite_klDiv_toReal_eq {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hfinite : InformationTheory.klDiv μ ν ≠ ∞) :
    (InformationTheory.klDiv μ ν).toReal =
      ∑ x : α, μ.real {x} * Real.log (μ.real {x} / ν.real {x}) := by
  have hac : μ ≪ ν := (InformationTheory.klDiv_ne_top_iff.mp hfinite).1
  rw [InformationTheory.toReal_klDiv_of_measure_eq hac (by simp),
    integral_fintype (Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hν : ν {x} = 0
  · have hμ : μ {x} = 0 := hac hν
    simp [measureReal_def, hμ, hν]
  · have hνtop : ν {x} ≠ ∞ := measure_ne_top ν {x}
    have hνr0 : ν.real {x} ≠ 0 := by
      rw [measureReal_def]
      exact ENNReal.toReal_ne_zero.2 ⟨hν, hνtop⟩
    have hrn : (μ.rnDeriv ν x).toReal = μ.real {x} / ν.real {x} := by
      have hc := congrArg ENNReal.toReal
        (Causalean.Stat.rnDeriv_mul_measure_singleton μ ν hac x)
      rw [ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def] at hc
      rw [eq_div_iff hνr0, mul_comm, hc]
    simp only [llr, hrn]
    rfl

private lemma finite_klDiv_toReal_eq_entropy {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hfinite : InformationTheory.klDiv μ ν ≠ ∞) :
    (InformationTheory.klDiv μ ν).toReal =
      - Causalean.Mathlib.InformationTheory.entropy (fun x : α => μ.real {x}) -
        ∑ x : α, μ.real {x} * Real.log (ν.real {x}) := by
  rw [finite_klDiv_toReal_eq μ ν hfinite,
    Causalean.Mathlib.InformationTheory.entropy_def]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have hac : μ ≪ ν := (InformationTheory.klDiv_ne_top_iff.mp hfinite).1
  by_cases hμ : μ.real {x} = 0
  · simp [hμ, Real.negMulLog]
  · have hν : ν.real {x} ≠ 0 := by
      intro h
      have hνenn : ν {x} = 0 := by
        by_contra hn
        exact (ENNReal.toReal_ne_zero.2 ⟨hn, measure_ne_top ν {x}⟩)
          (by simpa [measureReal_def] using h)
      have hμenn := hac hνenn
      exact hμ (by simp [measureReal_def, hμenn])
    rw [Real.log_div hμ hν, Real.negMulLog_def]
    ring

private lemma condEntropy_uniform_ge {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (q : α → Measure β) (ν : Measure β)
    [∀ j, IsProbabilityMeasure (q j)] [IsProbabilityMeasure ν]
    (hα : 0 < Fintype.card α)
    (hfinite : ∀ j, InformationTheory.klDiv (q j) ν ≠ ∞) :
    Real.log (Fintype.card α) - (Fintype.card α : ℝ)⁻¹ *
        ∑ j : α, (InformationTheory.klDiv (q j) ν).toReal ≤
      Causalean.Mathlib.InformationTheory.condEntropy
        (fun z : α × β => (Fintype.card α : ℝ)⁻¹ * (q z.1).real {z.2}) := by
  classical
  let c : ℝ := (Fintype.card α : ℝ)⁻¹
  let a : α → β → ℝ := fun j k => (q j).real {k}
  let r : β → ℝ := fun k => ν.real {k}
  let p : α × β → ℝ := fun z => c * a z.1 z.2
  let b : β → ℝ := fun k => ∑ j : α, p (j, k)
  have hcpos : 0 < c := by simp [c, hα]
  have hcsum : c * (Fintype.card α : ℝ) = 1 := by
    dsimp [c]
    field_simp
  have hasum (j : α) : ∑ k : β, a j k = 1 := by
    simp [a]
  have hrsum : ∑ k : β, r k = 1 := by simp [r]
  have ha0 (j : α) (k : β) : 0 ≤ a j k := measureReal_nonneg
  have hr0 (k : β) : 0 ≤ r k := measureReal_nonneg
  have hp0 (z : α × β) : 0 ≤ p z := mul_nonneg hcpos.le (ha0 _ _)
  have hpsum : ∑ z : α × β, p z = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [p, ← Finset.mul_sum, hasum]
    simp [hcsum]
  have hbdef (k : β) :
      Causalean.Mathlib.InformationTheory.yMarginal p k = b k := by
    rfl
  have hb0 (k : β) : 0 ≤ b k := Finset.sum_nonneg (fun j _ => hp0 (j, k))
  have hbsum : ∑ k : β, b k = 1 := by
    simpa [hbdef] using
      (Causalean.Mathlib.InformationTheory.yMarginal_sum (α := α) (β := β) hpsum)
  have hbr : ∀ k, b k ≠ 0 → 0 < r k := by
    intro k hbk
    have hex : ∃ j : α, a j k ≠ 0 := by
      by_contra hex
      have hall : ∀ j : α, a j k = 0 := by
        intro j
        by_contra hj
        exact hex ⟨j, hj⟩
      apply hbk
      simp [b, p, hall]
    obtain ⟨j, haj⟩ := hex
    have hac : q j ≪ ν := (InformationTheory.klDiv_ne_top_iff.mp (hfinite j)).1
    have hνenn : ν {k} ≠ 0 := by
      intro hz
      have hq := hac hz
      exact haj (by simp [a, measureReal_def, hq])
    exact lt_of_le_of_ne (hr0 k) (by
      intro hrz
      exact hνenn (by
        by_contra hn
        exact (ENNReal.toReal_ne_zero.2 ⟨hn, measure_ne_top ν {k}⟩)
          (by simpa [r, measureReal_def] using hrz.symm)))
  have hcross :
      Causalean.Mathlib.InformationTheory.entropy b ≤
        - ∑ k : β, b k * Real.log (r k) :=
    Causalean.Mathlib.InformationTheory.entropy_le_crossEntropy hb0 hr0
      (by rw [hbsum, hrsum]) hbr
  have hpEntropy :
      Causalean.Mathlib.InformationTheory.entropy p =
        Real.log (Fintype.card α) + c *
          ∑ j : α, Causalean.Mathlib.InformationTheory.entropy (a j) := by
    rw [Causalean.Mathlib.InformationTheory.entropy_def, Fintype.sum_prod_type]
    have hnegc : Real.negMulLog c = c * Real.log (Fintype.card α) := by
      dsimp [c]
      change -(Fintype.card α : ℝ)⁻¹ * Real.log (Fintype.card α : ℝ)⁻¹ = _
      rw [Real.log_inv]
      ring
    calc
      (∑ j : α, ∑ k : β, Real.negMulLog (p (j, k))) =
          ∑ j : α, ∑ k : β,
            (a j k * Real.negMulLog c + c * Real.negMulLog (a j k)) := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        simp [p, Real.negMulLog_mul]
      _ = ∑ j : α, (Real.negMulLog c +
          c * Causalean.Mathlib.InformationTheory.entropy (a j)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hasum,
          ← Finset.mul_sum]
        simp [Causalean.Mathlib.InformationTheory.entropy_def]
      _ = (Fintype.card α : ℝ) * Real.negMulLog c +
          c * ∑ j : α, Causalean.Mathlib.InformationTheory.entropy (a j) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Finset.mul_sum]
        simp
      _ = Real.log (Fintype.card α) +
          c * ∑ j : α, Causalean.Mathlib.InformationTheory.entropy (a j) := by
        rw [hnegc]
        have hsc : (Fintype.card α : ℝ) * c = 1 := by
          simpa [mul_comm] using hcsum
        rw [← mul_assoc, hsc, one_mul]
  have hlogsum :
      ∑ k : β, b k * Real.log (r k) =
        c * ∑ j : α, ∑ k : β, a j k * Real.log (r k) := by
    simp_rw [b, p, Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      (∑ j : α, ∑ k : β, c * a j k * Real.log (r k)) =
          ∑ j : α, c * ∑ k : β, a j k * Real.log (r k) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = c * ∑ j : α, ∑ k : β, a j k * Real.log (r k) := by
        rw [Finset.mul_sum]
  have hKL (j : α) :
      (InformationTheory.klDiv (q j) ν).toReal =
        - Causalean.Mathlib.InformationTheory.entropy (a j) -
          ∑ k : β, a j k * Real.log (r k) := by
    simpa [a, r] using finite_klDiv_toReal_eq_entropy (q j) ν (hfinite j)
  change Real.log (Fintype.card α) - c *
      ∑ j : α, (InformationTheory.klDiv (q j) ν).toReal ≤
    Causalean.Mathlib.InformationTheory.condEntropy p
  rw [Causalean.Mathlib.InformationTheory.condEntropy_def,
    show Causalean.Mathlib.InformationTheory.yMarginal p = b from funext hbdef,
    hpEntropy]
  have hmain :
      -Causalean.Mathlib.InformationTheory.entropy b ≥
        ∑ k : β, b k * Real.log (r k) := by linarith
  rw [hlogsum] at hmain
  have hKLsum :
      ∑ j : α, (InformationTheory.klDiv (q j) ν).toReal =
        - ∑ j : α, Causalean.Mathlib.InformationTheory.entropy (a j) -
          ∑ j : α, ∑ k : β, a j k * Real.log (r k) := by
    simp_rw [hKL, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [hKLsum]
  dsimp [c]
  rw [Causalean.Mathlib.InformationTheory.entropy_def] at hmain
  linarith

-- @node: lem:explicit-entropy-decoding-bound
/-- The explicit average-error Fano inequality, including the finite-`M`
constants used by the paper. -/
lemma explicit_entropy_decoding_bound (M : ℕ) (hM : 2 ≤ M)
    (Q : Fin (M + 1) → Measure Ω) (decoder : Ω → Fin (M + 1))
    (_hdecoder : Measurable decoder)
    (_hprob : ∀ j, IsProbabilityMeasure (Q j))
    (_hfinite : ∀ j, InformationTheory.klDiv (Q j) (Q 0) ≠ ∞) :
    (M + 1 : ℝ)⁻¹ * ∑ j : Fin (M + 1), (Q j {ω | decoder ω ≠ j}).toReal ≥
      (Real.log (M + 1) - (M + 1 : ℝ)⁻¹ *
        ∑ j : Fin (M + 1), (InformationTheory.klDiv (Q j) (Q 0)).toReal - Real.log 2) /
        Real.log M := by
  classical
  letI (j : Fin (M + 1)) : IsProbabilityMeasure (Q j) := _hprob j
  let q : Fin (M + 1) → Measure (Fin (M + 1)) := fun j => Q j |>.map decoder
  letI (j : Fin (M + 1)) : IsProbabilityMeasure (q j) := by
    refine ⟨?_⟩
    simp [q, Measure.map_apply _hdecoder MeasurableSet.univ]
  have hqfinite : ∀ j, InformationTheory.klDiv (q j) (q 0) ≠ ∞ := by
    intro j
    exact ne_top_of_le_ne_top
      (_hfinite j)
      (Causalean.Mathlib.InformationTheory.Measure.klDiv_map_le _hdecoder)
  let p : Fin (M + 1) × Fin (M + 1) → ℝ := fun z =>
    (M + 1 : ℝ)⁻¹ * (q z.1).real {z.2}
  have hp0 : ∀ z, 0 ≤ p z := fun z => mul_nonneg (by positivity) measureReal_nonneg
  have hpsum : ∑ z, p z = 1 := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ j : Fin (M + 1), ∑ k : Fin (M + 1), p (j, k)) =
          ∑ j : Fin (M + 1), (M + 1 : ℝ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [p]
        rw [← Finset.mul_sum, sum_measureReal_singleton]
        simp
      _ = 1 := by
        simp [show (M + 1 : ℝ) ≠ 0 by positivity]
  have hcond :
      Real.log (M + 1) - (M + 1 : ℝ)⁻¹ *
          ∑ j : Fin (M + 1), (InformationTheory.klDiv (q j) (q 0)).toReal ≤
        Causalean.Mathlib.InformationTheory.condEntropy p := by
    simpa [p] using condEntropy_uniform_ge q (q 0)
      (by simp) hqfinite
  have hfano := Causalean.Mathlib.InformationTheory.fano_inequality hp0 hpsum
    (show 2 ≤ Fintype.card (Fin (M + 1)) by simp; omega)
    (id : Fin (M + 1) → Fin (M + 1))
  have herr : Causalean.Mathlib.InformationTheory.errorProb p id =
      (M + 1 : ℝ)⁻¹ *
        ∑ j : Fin (M + 1), (Q j {ω | decoder ω ≠ j}).toReal := by
    rw [Causalean.Mathlib.InformationTheory.errorProb_def, Fintype.sum_prod_type]
    simp_rw [p]
    calc
      (∑ j : Fin (M + 1), ∑ k : Fin (M + 1),
          if j = id k then 0 else (M + 1 : ℝ)⁻¹ * (q j).real {k}) =
          (M + 1 : ℝ)⁻¹ * ∑ j : Fin (M + 1),
            ∑ k : Fin (M + 1), if j = k then 0 else (q j).real {k} := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        simp only [id_eq]
        split_ifs <;> ring
      _ = (M + 1 : ℝ)⁻¹ *
          ∑ j : Fin (M + 1), (Q j {ω | decoder ω ≠ j}).toReal := by
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        have hset : {ω | decoder ω ≠ j} =
            (decoder ⁻¹' ({j} : Set (Fin (M + 1))))ᶜ := by
          ext ω
          simp
        rw [hset]
        change (∑ k, if j = k then 0 else (q j).real {k}) =
          (Q j).real ((decoder ⁻¹' ({j} : Set (Fin (M + 1))))ᶜ)
        rw [measureReal_compl (_hdecoder (measurableSet_singleton j))]
        have hqmass : (q j).real {j} = (Q j).real (decoder ⁻¹' {j}) := by
          simp [q, Measure.map_apply _hdecoder (measurableSet_singleton j), measureReal_def]
        rw [show (Q j).real univ = 1 by simp [measureReal_def], ← hqmass]
        calc
          (∑ k, if j = k then 0 else (q j).real {k}) =
              ∑ k, ((q j).real {k} - if k = j then (q j).real {k} else 0) := by
            apply Finset.sum_congr rfl
            intro k _
            by_cases hjk : j = k
            · subst k
              simp
            · have hkj : k ≠ j := Ne.symm hjk
              rw [if_neg hjk, if_neg hkj]
              ring
          _ = (∑ k, (q j).real {k}) -
              ∑ k, (if k = j then (q j).real {k} else 0) := by
            rw [Finset.sum_sub_distrib]
          _ = 1 - (q j).real {j} := by
            rw [sum_measureReal_singleton]
            simp
  rw [herr] at hfano
  have hlogMpos : 0 < Real.log M :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by omega) hM))
  have hbin : Real.binEntropy
      ((M + 1 : ℝ)⁻¹ * ∑ j : Fin (M + 1), (Q j {ω | decoder ω ≠ j}).toReal) ≤
      Real.log 2 := Real.binEntropy_le_log_two
  have hklmap : ∑ j : Fin (M + 1),
      (InformationTheory.klDiv (q j) (q 0)).toReal ≤
      ∑ j : Fin (M + 1),
        (InformationTheory.klDiv (Q j) (Q 0)).toReal := by
    apply Finset.sum_le_sum
    intro j _
    exact ENNReal.toReal_mono (_hfinite j)
      (Causalean.Mathlib.InformationTheory.Measure.klDiv_map_le _hdecoder)
  rw [show (Fintype.card (Fin (M + 1)) : ℝ) - 1 = M by norm_num] at hfano
  change (Real.log (M + 1) - (M + 1 : ℝ)⁻¹ *
      ∑ j : Fin (M + 1), (InformationTheory.klDiv (Q j) (Q 0)).toReal - Real.log 2) /
      Real.log M ≤
    (M + 1 : ℝ)⁻¹ * ∑ j : Fin (M + 1), (Q j {ω | decoder ω ≠ j}).toReal
  rw [div_le_iff₀ hlogMpos]
  have hc : 0 ≤ (M + 1 : ℝ)⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hklmap hc, hcond, hfano, hbin]

-- @node: finiteSeparatedDecoder
/-- Decode to the unique parameter lying within the separation radius, with
index zero as fallback when no such parameter exists. -/
noncomputable def finiteSeparatedDecoder {N : ℕ} (v : Fin (N + 1) → V) (δ : ℝ)
    (estimate : Ω → V) (ω : Ω) : Fin (N + 1) :=
  if h : ∃ j, dist (estimate ω) (v j) < δ then Classical.choose h else 0

-- @node: finiteSeparatedDecoder_eq_of_lt
lemma finiteSeparatedDecoder_eq_of_lt {N : ℕ} (v : Fin (N + 1) → V) (δ : ℝ)
    (estimate : Ω → V) (hsep : ∀ j k, j ≠ k → 2 * δ ≤ dist (v j) (v k))
    (ω : Ω) (j : Fin (N + 1)) (hj : dist (estimate ω) (v j) < δ) :
    finiteSeparatedDecoder v δ estimate ω = j := by
  rw [finiteSeparatedDecoder, dif_pos ⟨j, hj⟩]
  by_contra hne
  have hk := Classical.choose_spec
    (show ∃ k, dist (estimate ω) (v k) < δ from ⟨j, hj⟩)
  have htriangle :
      dist (v (Classical.choose
        (show ∃ k, dist (estimate ω) (v k) < δ from ⟨j, hj⟩))) (v j) < 2 * δ := by
    calc
      dist (v (Classical.choose
          (show ∃ k, dist (estimate ω) (v k) < δ from ⟨j, hj⟩))) (v j)
          ≤ dist (v (Classical.choose
              (show ∃ k, dist (estimate ω) (v k) < δ from ⟨j, hj⟩))) (estimate ω) +
              dist (estimate ω) (v j) := dist_triangle _ _ _
      _ < 2 * δ := by rw [dist_comm (v _)]; linarith
  exact (not_lt_of_ge (hsep _ _ hne)) htriangle

-- @node: measurable_finiteSeparatedDecoder
lemma measurable_finiteSeparatedDecoder {N : ℕ} (v : Fin (N + 1) → V) (δ : ℝ)
    (estimate : Ω → V) (hest : Measurable estimate)
    (hsep : ∀ j k, j ≠ k → 2 * δ ≤ dist (v j) (v k)) :
    Measurable (finiteSeparatedDecoder v δ estimate) := by
  apply measurable_to_countable'
  intro j
  have hball : ∀ k : Fin (N + 1),
      MeasurableSet {ω | dist (estimate ω) (v k) < δ} := by
    intro k
    have herr := Causalean.Stat.measurableSet_error hest (v k) δ
    simpa only [compl_setOf, not_le] using herr.compl
  by_cases hj : j = 0
  · subst j
    have heq : finiteSeparatedDecoder v δ estimate ⁻¹' {0} =
        {ω | dist (estimate ω) (v 0) < δ} ∪
          (⋃ k : Fin (N + 1), {ω | dist (estimate ω) (v k) < δ})ᶜ := by
      ext ω
      simp only [mem_preimage, mem_singleton_iff, mem_union, mem_setOf_eq,
        mem_compl_iff, mem_iUnion, not_exists]
      constructor
      · intro hd
        by_cases h0 : dist (estimate ω) (v 0) < δ
        · exact Or.inl h0
        · right
          intro k hk
          have := finiteSeparatedDecoder_eq_of_lt v δ estimate hsep ω k hk
          rw [hd] at this
          exact h0 (this ▸ hk)
      · rintro (h0 | hall)
        · exact finiteSeparatedDecoder_eq_of_lt v δ estimate hsep ω 0 h0
        · rw [finiteSeparatedDecoder, dif_neg]
          exact fun hex => by rcases hex with ⟨k, hk⟩; exact hall k hk
    rw [heq]
    exact (hball 0).union (MeasurableSet.iUnion hball).compl
  · have heq : finiteSeparatedDecoder v δ estimate ⁻¹' {j} =
        {ω | dist (estimate ω) (v j) < δ} := by
      ext ω
      simp only [mem_preimage, mem_singleton_iff, mem_setOf_eq]
      constructor
      · intro hd
        rw [finiteSeparatedDecoder] at hd
        split at hd
        · have hc := Classical.choose_spec ‹∃ j, dist (estimate ω) (v j) < δ›
          simpa [hd] using hc
        · exact False.elim (hj hd.symm)
      · exact finiteSeparatedDecoder_eq_of_lt v δ estimate hsep ω j
    rw [heq]
    exact hball j

-- @node: finiteSeparatedDecoder_error_imp
lemma finiteSeparatedDecoder_error_imp {N : ℕ} (v : Fin (N + 1) → V) (δ : ℝ)
    (estimate : Ω → V) (hsep : ∀ j k, j ≠ k → 2 * δ ≤ dist (v j) (v k))
    (ω : Ω) (j : Fin (N + 1))
    (herr : finiteSeparatedDecoder v δ estimate ω ≠ j) :
    δ ≤ dist (estimate ω) (v j) := by
  by_contra hlt
  exact herr (finiteSeparatedDecoder_eq_of_lt v δ estimate hsep ω j
    (lt_of_not_ge hlt))

-- @node: decoderErrorProbability_mul_le_lintegral
lemma decoderErrorProbability_mul_le_lintegral {N : ℕ}
    (Q : Fin (N + 1) → Measure Ω) (v : Fin (N + 1) → V) (δ : ℝ)
    (estimate : Ω → V) (hest : Measurable estimate)
    (hsep : ∀ j k, j ≠ k → 2 * δ ≤ dist (v j) (v k)) (j : Fin (N + 1)) :
    ENNReal.ofReal δ * Q j {ω | finiteSeparatedDecoder v δ estimate ω ≠ j} ≤
      ∫⁻ ω, ENNReal.ofReal (dist (estimate ω) (v j)) ∂Q j := by
  let E : Set Ω := {ω | finiteSeparatedDecoder v δ estimate ω ≠ j}
  have hE : MeasurableSet E := by
    exact ((measurable_finiteSeparatedDecoder v δ estimate hest hsep)
      (measurableSet_singleton j)).compl
  calc
    ENNReal.ofReal δ * Q j E = ∫⁻ _ in E, ENNReal.ofReal δ ∂Q j := by
      rw [setLIntegral_const E]
    _ ≤ ∫⁻ ω in E, ENNReal.ofReal (dist (estimate ω) (v j)) ∂Q j := by
      apply setLIntegral_mono
      · fun_prop
      intro ω hω
      exact ENNReal.ofReal_le_ofReal
        (finiteSeparatedDecoder_error_imp v δ estimate hsep ω j hω)
    _ ≤ ∫⁻ ω, ENNReal.ofReal (dist (estimate ω) (v j)) ∂Q j :=
      setLIntegral_le_lintegral E _

-- @node: distanceEventProbability_mul_le_lintegral
lemma distanceEventProbability_mul_le_lintegral (μ : Measure Ω) (θ : V) (δ : ℝ)
    (estimate : Ω → V) (hest : Measurable estimate) :
    ENNReal.ofReal δ * μ {ω | δ ≤ dist (estimate ω) θ} ≤
      ∫⁻ ω, ENNReal.ofReal (dist (estimate ω) θ) ∂μ := by
  let E : Set Ω := {ω | δ ≤ dist (estimate ω) θ}
  have hE : MeasurableSet E := Causalean.Stat.measurableSet_error hest θ δ
  calc
    ENNReal.ofReal δ * μ E = ∫⁻ _ in E, ENNReal.ofReal δ ∂μ := by
      rw [setLIntegral_const E]
    _ ≤ ∫⁻ ω in E, ENNReal.ofReal (dist (estimate ω) θ) ∂μ := by
      apply setLIntegral_mono
      · fun_prop
      intro ω hω
      exact ENNReal.ofReal_le_ofReal hω
    _ ≤ ∫⁻ ω, ENNReal.ofReal (dist (estimate ω) θ) ∂μ :=
      setLIntegral_le_lintegral E _

-- @node: lem:finite-information-testing
/-- Separated parameters under a two-point or average-KL budget force a
fixed fraction of the separation as maximal expected loss. -/
lemma finite_information_testing :
    ∃ c : ℝ, 0 < c ∧ ∀ (M : ℕ) (Q : Fin (M + 1) → Measure Ω)
      (v : Fin (M + 1) → V) (δ a : ℝ),
      0 < δ →
      (∀ j, IsProbabilityMeasure (Q j)) →
      (∀ j, InformationTheory.klDiv (Q j) (Q 0) ≠ ∞) →
      (∀ j k, j ≠ k → 2 * δ ≤ dist (v j) (v k)) →
      ((M = 1 ∧ InformationTheory.klDiv (Q 1) (Q 0) ≤ ENNReal.ofReal (1 / 8)) ∨
        (2 ≤ M ∧ 0 < a ∧ a < 1 / 8 ∧
          (M : ℝ≥0∞)⁻¹ * ∑ j : Fin M,
            InformationTheory.klDiv (Q j.succ) (Q 0) ≤
              ENNReal.ofReal (a * Real.log M))) →
      ∀ estimate : Ω → V, Measurable estimate →
        ENNReal.ofReal (c * δ) ≤
          ⨆ j : Fin (M + 1), ∫⁻ ω,
            ENNReal.ofReal (dist (estimate ω) (v j)) ∂Q j := by
  refine ⟨1 / 8, by norm_num, ?_⟩
  intro M Q v δ a hδ hprob hfinite hsep hinfo estimate hest
  letI : ∀ j, IsProbabilityMeasure (Q j) := fun j => hprob j
  rcases hinfo with htwo | hmany
  · rcases htwo with ⟨rfl, hkl⟩
    have hac : Q 1 ≪ Q 0 := (InformationTheory.klDiv_ne_top_iff.mp (hfinite 1)).1
    have hlecam := Causalean.Stat.klForm_two_point_lower_bound
      (P₀ := Q 1) (P₁ := Q 0) hac (hfinite 1) hest (hsep 1 0 (by decide))
    have hklreal : (InformationTheory.klDiv (Q 1) (Q 0)).toReal ≤ 1 / 8 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hkl
      simpa using this
    have hsqrt : Real.sqrt
        ((InformationTheory.klDiv (Q 1) (Q 0)).toReal / 2) ≤ 1 / 4 := by
      rw [Real.sqrt_le_iff]
      constructor
      · norm_num
      · nlinarith
    have herr : 3 / 8 ≤ max
        ((Q 1).real {ω | δ ≤ dist (estimate ω) (v 1)})
        ((Q 0).real {ω | δ ≤ dist (estimate ω) (v 0)}) := by
      linarith
    rcases (le_max_iff.mp herr) with herr | herr
    · calc
        ENNReal.ofReal ((1 / 8) * δ) ≤
            ENNReal.ofReal δ * Q 1 {ω | δ ≤ dist (estimate ω) (v 1)} := by
              change 3 / 8 ≤
                (Q 1 {ω | δ ≤ dist (estimate ω) (v 1)}).toReal at herr
              rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 8)]
              rw [mul_comm (ENNReal.ofReal δ)]
              gcongr
              rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
              nlinarith
        _ ≤ ∫⁻ ω, ENNReal.ofReal (dist (estimate ω) (v 1)) ∂Q 1 :=
          distanceEventProbability_mul_le_lintegral (Q 1) (v 1) δ estimate hest
        _ ≤ ⨆ j : Fin 2, ∫⁻ ω,
            ENNReal.ofReal (dist (estimate ω) (v j)) ∂Q j := by
          exact le_iSup (fun j : Fin 2 => ∫⁻ ω,
            ENNReal.ofReal (dist (estimate ω) (v j)) ∂Q j) 1
    · calc
        ENNReal.ofReal ((1 / 8) * δ) ≤
            ENNReal.ofReal δ * Q 0 {ω | δ ≤ dist (estimate ω) (v 0)} := by
              change 3 / 8 ≤
                (Q 0 {ω | δ ≤ dist (estimate ω) (v 0)}).toReal at herr
              rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 8)]
              rw [mul_comm (ENNReal.ofReal δ)]
              gcongr
              rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
              nlinarith
        _ ≤ ∫⁻ ω, ENNReal.ofReal (dist (estimate ω) (v 0)) ∂Q 0 :=
          distanceEventProbability_mul_le_lintegral (Q 0) (v 0) δ estimate hest
        _ ≤ ⨆ j : Fin 2, ∫⁻ ω,
            ENNReal.ofReal (dist (estimate ω) (v j)) ∂Q j := by
          exact le_iSup (fun j : Fin 2 => ∫⁻ ω,
            ENNReal.ofReal (dist (estimate ω) (v j)) ∂Q j) 0
  · rcases hmany with ⟨hM, ha0, ha, hbudget⟩
    let decoder := finiteSeparatedDecoder v δ estimate
    have hdecoder : Measurable decoder :=
      measurable_finiteSeparatedDecoder v δ estimate hest hsep
    have hfano := explicit_entropy_decoding_bound M hM Q decoder hdecoder hprob hfinite
    have hMpos : (0 : ℝ) < M := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) hM)
    have hlogM : 0 < Real.log M := Real.log_pos (by exact_mod_cast hM)
    have hbudgetR : (M : ℝ)⁻¹ * ∑ j : Fin M,
        (InformationTheory.klDiv (Q j.succ) (Q 0)).toReal ≤ a * Real.log M := by
      have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbudget
      rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
        ENNReal.toReal_sum] at ht
      · simpa [ENNReal.toReal_ofReal
          (mul_nonneg (le_of_lt ha0) (le_of_lt hlogM))] using ht
      · intro j _
        exact hfinite j.succ
    have hsum : ∑ j : Fin (M + 1),
        (InformationTheory.klDiv (Q j) (Q 0)).toReal ≤ M * (a * Real.log M) := by
      rw [Fin.sum_univ_succ, InformationTheory.klDiv_self,
        ENNReal.toReal_zero, zero_add]
      rw [inv_mul_le_iff₀ hMpos] at hbudgetR
      simpa [mul_assoc] using hbudgetR
    have havgkl : (M + 1 : ℝ)⁻¹ * ∑ j : Fin (M + 1),
        (InformationTheory.klDiv (Q j) (Q 0)).toReal ≤ a * Real.log M := by
      rw [inv_mul_eq_div]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < M + 1)).2
      nlinarith [mul_pos ha0 hlogM]
    have hsquare : (4 : ℝ) * M ≤ (M + 1 : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((M : ℝ) - 1)]
    have hlog_square := Real.log_le_log (mul_pos (by norm_num) hMpos) hsquare
    have hhalf : Real.log M / 2 + Real.log 2 ≤ Real.log (M + 1) := by
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hMpos),
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow,
        Real.log_pow] at hlog_square
      norm_num at hlog_square ⊢
      nlinarith
    have herror : 3 / 8 ≤ (M + 1 : ℝ)⁻¹ *
        ∑ j : Fin (M + 1), (Q j {ω | decoder ω ≠ j}).toReal := by
      have hrhs : 3 / 8 ≤
          (Real.log (M + 1) - (M + 1 : ℝ)⁻¹ *
            ∑ j : Fin (M + 1),
              (InformationTheory.klDiv (Q j) (Q 0)).toReal - Real.log 2) /
            Real.log M := by
        apply (le_div_iff₀ hlogM).2
        nlinarith
      exact hrhs.trans hfano
    have hsome : ∃ j : Fin (M + 1), 3 / 8 ≤
        (Q j {ω | decoder ω ≠ j}).toReal := by
      by_contra hall
      push_neg at hall
      have hsumlt : ∑ j : Fin (M + 1), (Q j {ω | decoder ω ≠ j}).toReal <
          (M + 1 : ℝ) * (3 / 8) := by
        calc
          ∑ j : Fin (M + 1), (Q j {ω | decoder ω ≠ j}).toReal <
              ∑ _j : Fin (M + 1), (3 / 8 : ℝ) :=
            Finset.sum_lt_sum (fun j _ => (hall j).le)
              ⟨0, Finset.mem_univ _, hall 0⟩
          _ = (M + 1 : ℝ) * (3 / 8) := by simp
      rw [inv_mul_eq_div] at herror
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < M + 1)).mp herror
      nlinarith
    rcases hsome with ⟨j, hj⟩
    calc
      ENNReal.ofReal ((1 / 8) * δ) ≤
          ENNReal.ofReal δ * Q j {ω | decoder ω ≠ j} := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 8)]
        rw [mul_comm (ENNReal.ofReal δ)]
        gcongr
        rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
        nlinarith
      _ ≤ ∫⁻ ω, ENNReal.ofReal (dist (estimate ω) (v j)) ∂Q j :=
        decoderErrorProbability_mul_le_lintegral Q v δ estimate hest hsep j
      _ ≤ ⨆ j : Fin (M + 1), ∫⁻ ω,
          ENNReal.ofReal (dist (estimate ω) (v j)) ∂Q j := by
        exact le_iSup (fun j : Fin (M + 1) => ∫⁻ ω,
          ENNReal.ofReal (dist (estimate ω) (v j)) ∂Q j) j

end CausalSmith.Stat.BddThicknessEstimabilityFrontier
