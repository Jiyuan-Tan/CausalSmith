import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.IIDPoisson
import Causalean.Mathlib.Probability.Kernel.GraphMapProd


import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Finite Poisson samples

This file turns an independent Poisson count and infinite i.i.d. stream into a
genuine finite sequence.  It records the count law and the exact, unnormalised
fixed-count fibre law.  The latter is the convenient measure-theoretic form of
the statement that, conditional on the count, the observations are i.i.d.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- The Poisson law with mean `r` gives the single count `n` exactly the Poisson
probability mass at `n`.

This bridge used to hold by definition, because the Poisson law was *defined* as
the measure attached to the Poisson mass function.  Mathlib now defines it
primitively, as a weighted sum of point masses, so the two descriptions have to
be reconciled explicitly.  Every result phrased against the mass function needs
this lemma to be transported to the Poisson law, so it is stated once here for
the whole `FiniteMarkedPoissonPartition` family rather than re-proved per file. -/
lemma poissonMeasure_singleton_eq_poissonPMF (r : ℝ≥0) (n : ℕ) :
    poissonMeasure r {n} = poissonPMF r n := by
  rw [poissonMeasure_singleton, ← poissonPMFReal_ofReal_eq_poissonPMF]
  rfl

variable {X : Type*} [MeasurableSpace X]

/-- For [an observation space](hyp:X), a [finite sample](goal) is a nonnegative integer sample size together with one observation for each position below that size. -/
abbrev FiniteSample (X : Type*) [MeasurableSpace X] := Σ n : ℕ, Fin n → X

/-- The number of observations in a finite sequence. -/
def FiniteSample.count (s : FiniteSample X) : ℕ := s.1

/-- The coordinates of a finite sequence at its dependent finite index type. -/
def FiniteSample.points (s : FiniteSample X) : Fin s.count → X := s.2

/-- Given [a nonnegative integer sample size](hyp:n) and [a tuple of observations indexed by its positions](hyp:x), the [fixed-size embedding](goal) is the finite sample having that size and those observations. -/
def fixedSizeEmbed (n : ℕ) (x : Fin n → X) : FiniteSample X := ⟨n, x⟩

/-- Given [a pair consisting of a nonnegative integer and an infinite observation stream](hyp:z), the [associated finite sample](goal) has that integer as its size and retains exactly the corresponding initial segment of the stream. -/
def streamToFiniteSample (z : ℕ × (ℕ → X)) : FiniteSample X :=
  ⟨z.1, fun i => z.2 i⟩

/-- Embedding a fixed-size tuple into the finite-sequence space is measurable. -/
@[fun_prop]
lemma measurable_fixedSizeEmbed (n : ℕ) : Measurable (fixedSizeEmbed (X := X) n) := by
  change Measurable (Sigma.mk n)
  apply Measurable.of_le_map
  exact iInf_le _ n

/-- Reading the count of a finite sequence is measurable. -/
@[fun_prop]
lemma measurable_finiteSample_count : Measurable (FiniteSample.count : FiniteSample X → ℕ) := by
  apply measurable_to_countable'
  intro n
  change MeasurableSet ({s : FiniteSample X | s.1 = n})
  rw [MeasurableSpace.measurableSet_iInf]
  intro m
  change MeasurableSet ((Sigma.mk m) ⁻¹' {s : FiniteSample X | s.1 = n})
  by_cases hmn : m = n
  · subst m
    simp
  · convert MeasurableSet.empty using 1
    ext x
    simp [hmn]

/-- Truncating a count-and-stream outcome to its selected prefix is measurable. -/
@[fun_prop]
lemma measurable_streamToFiniteSample :
    Measurable (streamToFiniteSample : (ℕ × (ℕ → X)) → FiniteSample X) := by
  intro s hs
  rw [MeasurableSpace.measurableSet_iInf] at hs
  rw [show streamToFiniteSample ⁻¹' s =
      ⋃ n : ℕ, {z : ℕ × (ℕ → X) | z.1 = n} ∩
        (fun z : ℕ × (ℕ → X) => fun i : Fin n => z.2 i) ⁻¹'
          (fixedSizeEmbed n ⁻¹' s) by
    ext z
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_setOf_eq]
    constructor
    · intro hz
      exact ⟨z.1, rfl, hz⟩
    · rintro ⟨n, hn, hz⟩
      subst n
      exact hz]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.inter
  · exact measurable_fst (measurableSet_singleton n)
  · have hsn : MeasurableSet (fixedSizeEmbed n ⁻¹' s) := hs n
    exact hsn.preimage (by fun_prop)

/-- Given [a probability measure on the observation space](hyp:P) and [a nonnegative Poisson mean](hyp:lam), the [finite Poisson sample law](goal) is the distribution obtained by drawing a Poisson count with that mean and an independent infinite sequence of independent observations from that probability measure, then retaining the initial segment selected by the count. -/
noncomputable def finitePoissonSampleLaw (P : Measure X) [IsProbabilityMeasure P]
    (lam : ℝ≥0) : Measure (FiniteSample X) :=
  Measure.map streamToFiniteSample (poissonIIDStreamLaw P lam)

/-- Let the observation space be equipped with a $\sigma$-algebra.  For [a probability measure on that space](hyp:P) and [a nonnegative Poisson mean](hyp:lam), [the assertion that the finite Poisson sample law is a probability measure](goal) holds. -/
instance finitePoissonSampleLaw_isProbabilityMeasure (P : Measure X) [IsProbabilityMeasure P]
    (lam : ℝ≥0) : IsProbabilityMeasure (finitePoissonSampleLaw P lam) := by
  unfold finitePoissonSampleLaw
  exact Measure.isProbabilityMeasure_map measurable_streamToFiniteSample.aemeasurable

/-- The count of a finite Poisson sample has scalar Poisson law with the
requested mean. -/
lemma finitePoissonSampleLaw_map_count (P : Measure X) [IsProbabilityMeasure P]
    (lam : ℝ≥0) :
    Measure.map FiniteSample.count (finitePoissonSampleLaw P lam) = poissonMeasure lam := by
  unfold finitePoissonSampleLaw
  rw [Measure.map_map measurable_finiteSample_count measurable_streamToFiniteSample]
  change Measure.map Prod.fst (poissonIIDStreamLaw P lam) = poissonMeasure lam
  exact poissonIIDStreamLaw_map_count P lam

/-- On the fibre where the count equals `n`, the finite Poisson law is the
Poisson mass at `n` times the embedded `n`-fold product law. -/
lemma finitePoissonSampleLaw_restrict_count_eq (P : Measure X) [IsProbabilityMeasure P]
    (lam : ℝ≥0) (n : ℕ) :
    (finitePoissonSampleLaw P lam).restrict
        (FiniteSample.count ⁻¹' ({n} : Set ℕ)) =
      (poissonMeasure lam) ({n} : Set ℕ) •
        Measure.map (fixedSizeEmbed n) (Measure.pi (fun _ : Fin n => P)) := by
  unfold finitePoissonSampleLaw poissonIIDStreamLaw
  rw [Measure.restrict_map measurable_streamToFiniteSample
    (measurable_finiteSample_count (X := X) (measurableSet_singleton n))]
  have hpre : streamToFiniteSample ⁻¹'
      (FiniteSample.count ⁻¹' ({n} : Set ℕ)) =
      ({n} : Set ℕ) ×ˢ (Set.univ : Set (ℕ → X)) := by
    ext z
    simp [streamToFiniteSample, FiniteSample.count]
  rw [hpre, ← Measure.restrict_prod_eq_prod_univ, Measure.restrict_singleton,
    Measure.prod_smul_left, Measure.map_smul, Measure.dirac_prod,
    Measure.map_map measurable_streamToFiniteSample (by fun_prop)]
  change (poissonMeasure lam) {n} •
      Measure.map (fixedSizeEmbed n ∘ fun z : ℕ → X => fun i : Fin n => z i)
        (iidStreamLaw P) = _
  rw [← Measure.map_map (measurable_fixedSizeEmbed n) (by fun_prop),
    iidStreamLaw_map_finPrefix]

/-- Given [a probability measure for observations](hyp:P), [a probability measure for real-valued marks](hyp:R), and [a nonnegative Poisson mean](hyp:lam), the [finite marked Poisson sample law](goal) is the finite Poisson sample law whose independent observation--mark pairs have the product of those two measures as their common distribution. -/
noncomputable def finiteMarkedPoissonSampleLaw (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0) :
    Measure (FiniteSample (X × ℝ)) :=
  finitePoissonSampleLaw (P.prod R) lam

/-- Let the observation space be equipped with a $\sigma$-algebra.  For [a probability measure on the observation space](hyp:P), [a probability measure on real-valued marks](hyp:R), and [a nonnegative Poisson mean](hyp:lam), [the assertion that the finite marked Poisson sample law is a probability measure](goal) holds. -/
instance finiteMarkedPoissonSampleLaw_isProbabilityMeasure
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0) :
    IsProbabilityMeasure (finiteMarkedPoissonSampleLaw P R lam) := by
  unfold finiteMarkedPoissonSampleLaw
  infer_instance

/-- The count of a finite marked Poisson sample has scalar Poisson law with
mean `lam`. -/
lemma finiteMarkedPoissonSampleLaw_map_count
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0) :
    Measure.map FiniteSample.count (finiteMarkedPoissonSampleLaw P R lam) =
      poissonMeasure lam := by
  exact finitePoissonSampleLaw_map_count (P.prod R) lam

/-- Fix [a nonnegative Poisson rate `lam`](hyp:lam). For an observation law `P` and
an independent mark law `R`, [restricting the finite marked Poisson sample law to
the event that the observed count equals `n` yields exactly `poissonMeasure lam
{n}` times the pushforward, under the fixed-size embedding, of `n` independent
draws from the product measure `P.prod R`](goal). -/
lemma finiteMarkedPoissonSampleLaw_restrict_count_eq
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0) (n : ℕ) :
    (finiteMarkedPoissonSampleLaw P R lam).restrict
        (FiniteSample.count ⁻¹' ({n} : Set ℕ)) =
      (poissonMeasure lam) ({n} : Set ℕ) •
        Measure.map (fixedSizeEmbed n)
          (Measure.pi (fun _ : Fin n => P.prod R)) := by
  exact finitePoissonSampleLaw_restrict_count_eq (P.prod R) lam n

end Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-! ## Capped prefixes and their restricted Poisson law -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition


variable {X : Type*} [MeasurableSpace X]

/-- Given [a fixed array](hyp:x), [a requested prefix length](hyp:m), and
[a proof that the request fits in the array](hyp:h), the [finite sample
consisting of exactly that prefix](goal) retains the first `m` coordinates. -/
def prefixOfLE {n : ℕ} (x : Fin n → X) (m : ℕ) (h : m ≤ n) : FiniteSample X :=
  ⟨m, fun i ↦ x ⟨i, lt_of_lt_of_le i.isLt h⟩⟩

/-- For [a fixed array](hyp:x) and [a requested length](hyp:m), the [capped
prefix](goal) is the genuine prefix in the right summand when the request fits
and the distinguished left summand on
overflow, so overflow is never confused with an empty observation. -/
def cappedPrefix {n : ℕ} (x : Fin n → X) (m : ℕ) : Unit ⊕ FiniteSample X :=
  if h : m ≤ n then Sum.inr (prefixOfLE x m h) else Sum.inl ()

/-- For [an overflow finite sample](hyp:overflow), [a fixed array](hyp:x), and
[a requested length](hyp:m), the [totalized capped prefix](goal) agrees with
the genuine prefix off overflow and uses the specified value on overflow. -/
def totalizedPrefix {n : ℕ} (overflow : FiniteSample X)
    (x : Fin n → X) (m : ℕ) : FiniteSample X :=
  Sum.elim (fun _ ↦ overflow) id (cappedPrefix x m)

/-- For [a fixed admissible length](hyp:m,h), [taking that prefix](goal) is a
measurable map of the fixed array. -/
@[fun_prop]
theorem measurable_prefixOfLE {n m : ℕ} (h : m ≤ n) :
    Measurable (fun x : Fin n → X ↦ prefixOfLE x m h) := by
  -- Compose `measurable_fixedSizeEmbed` with the coordinate restriction map.
  apply (measurable_fixedSizeEmbed m).comp
  fun_prop

/-- For fixed [array length](hyp:n), [the option-valued capped prefix is jointly
measurable in the array and requested count](goal), with the left summand recording every
overflow outcome. -/
@[fun_prop]
theorem measurable_cappedPrefix (n : ℕ) :
    Measurable (fun z : (Fin n → X) × ℕ ↦ cappedPrefix z.1 z.2) := by
  -- Partition the countable count coordinate into the measurable fibres `{m}`.
  apply measurable_from_prod_countable_left
  intro m
  unfold cappedPrefix
  change Measurable (fun x : Fin n → X ↦
    if h : m ≤ n then Sum.inr (prefixOfLE x m h) else Sum.inl ())
  split
  · exact measurable_inr.comp (measurable_prefixOfLE (X := X) ‹m ≤ n›)
  · fun_prop

/-- For [a specified overflow sample](hyp:overflow), [the map from a fixed
array and count to its totalized capped prefix](goal) is measurable. -/
@[fun_prop]
theorem measurable_totalizedPrefix {n : ℕ} (overflow : FiniteSample X) :
    Measurable (fun z : (Fin n → X) × ℕ ↦ totalizedPrefix overflow z.1 z.2) := by
  -- Compose `measurable_cappedPrefix` with measurable sum elimination.
  exact (measurable_const.sumElim measurable_id).comp (measurable_cappedPrefix n)

private lemma map_prefixCoordinates_pi (P : Measure X) [IsProbabilityMeasure P]
    {n m : ℕ} (h : m ≤ n) :
    Measure.map (fun x : Fin n → X ↦ fun i : Fin m ↦
        x ⟨i, lt_of_lt_of_le i.isLt h⟩)
      (Measure.pi (fun _ : Fin n ↦ P)) = Measure.pi (fun _ : Fin m ↦ P) := by
  classical
  symm
  refine Measure.pi_eq (μ := fun _ : Fin m ↦ P) (fun s hs ↦ ?_)
  rw [Measure.map_apply (by fun_prop) (.univ_pi hs)]
  have hpre : (fun x : Fin n → X ↦ fun i : Fin m ↦
        x ⟨i, lt_of_lt_of_le i.isLt h⟩) ⁻¹' (Set.univ.pi s) =
      Set.univ.pi (fun j : Fin n ↦
        if hj : j.val < m then s ⟨j.val, hj⟩ else Set.univ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hx j
      split
      · exact hx ⟨j.val, ‹j.val < m›⟩
      · trivial
    · intro hx i
      simpa using hx ⟨i.val, lt_of_lt_of_le i.isLt h⟩
  rw [hpre, Measure.pi_pi]
  let t : Finset (Fin n) := Finset.univ.filter fun j ↦ j.val < m
  have ht (j : t) : j.val.val < m := by
    simpa only [t, Finset.mem_filter, Finset.mem_univ, true_and] using j.property
  let e : Fin m ≃ t :=
    { toFun := fun i ↦ ⟨⟨i.val, lt_of_lt_of_le i.isLt h⟩, by simp [t, i.isLt]⟩
      invFun := fun j ↦ ⟨j.val.val, ht j⟩
      left_inv := fun i ↦ by rfl
      right_inv := fun j ↦ by ext; rfl }
  calc
    (∏ j : Fin n, P (if hj : j.val < m then s ⟨j.val, hj⟩ else Set.univ)) =
        ∏ j : Fin n, if hj : j.val < m then P (s ⟨j.val, hj⟩) else 1 := by
          apply Fintype.prod_congr
          intro j
          split <;> simp
    _ = ∏ j : t, P (s ⟨j.val.val, ht j⟩) := by
      rw [Finset.prod_dite]
      simp only [Finset.prod_const_one, mul_one]
      apply Fintype.prod_congr
      intro j
      congr 2
    _ = ∏ i : Fin m, P (s i) := by
      symm
      apply Fintype.prod_equiv e
      intro i
      rfl

/-- For [an observation probability law](hyp:P), [a Poisson mean](hyp:lambda),
for [a fixed sample size](hyp:n), and
[an arbitrary overflow totalization](hyp:overflow), [the totalized prefix
of that many iid observations and an independent Poisson count, restricted to
nonoverflow, has exactly the finite Poisson sample law restricted to counts at
most `n`](goal). -/
theorem map_totalizedPrefix_restrict_nonoverflow
    (P : Measure X) [IsProbabilityMeasure P] (lambda : ℝ≥0)
    (n : ℕ) (overflow : FiniteSample X) :
    Measure.map (fun z : (Fin n → X) × ℕ ↦
        totalizedPrefix overflow z.1 z.2)
      (((Measure.pi (fun _ : Fin n ↦ P)).prod (poissonMeasure lambda)).restrict
        (Prod.snd ⁻¹' Set.Iic n)) =
      (finitePoissonSampleLaw P lambda).restrict
        (FiniteSample.count ⁻¹' Set.Iic n) := by
  -- Decompose both restrictions as the countable sum over `m : Iic n`.
  -- On each fibre, product restriction and `finitePoissonSampleLaw_restrict_count_eq`
  -- both reduce to the Poisson atom at `m` times the map of the same `m`-prefix law.
  classical
  let Qn : Measure (Fin n → X) := Measure.pi (fun _ : Fin n ↦ P)
  let μ : Measure ((Fin n → X) × ℕ) := Qn.prod (poissonMeasure lambda)
  let ν : Measure (FiniteSample X) := finitePoissonSampleLaw P lambda
  let f : ((Fin n → X) × ℕ) → FiniteSample X := fun z ↦
    totalizedPrefix overflow z.1 z.2
  have hf : Measurable f := measurable_totalizedPrefix overflow
  have hfiber (m : Fin (n + 1)) :
      Measure.map f (μ.restrict (Prod.snd ⁻¹' ({m.val} : Set ℕ))) =
        ν.restrict (FiniteSample.count ⁻¹' ({m.val} : Set ℕ)) := by
    have hm : m.val ≤ n := Nat.le_of_lt_succ m.isLt
    have hs : Prod.snd ⁻¹' ({m.val} : Set ℕ) =
        (Set.univ : Set (Fin n → X)) ×ˢ ({m.val} : Set ℕ) := by
      ext z
      simp
    rw [finitePoissonSampleLaw_restrict_count_eq]
    rw [hs, ← Measure.prod_restrict, Measure.restrict_univ,
      Measure.restrict_singleton, Measure.prod_smul_right, Measure.map_smul,
      Measure.prod_dirac, Measure.map_map hf (by fun_prop)]
    have hfun : f ∘ (fun x : Fin n → X ↦ (x, m.val)) =
        fixedSizeEmbed m.val ∘ (fun x : Fin n → X ↦ fun i : Fin m.val ↦
          x ⟨i, lt_of_lt_of_le i.isLt hm⟩) := by
      funext x
      simp [f, totalizedPrefix, cappedPrefix, hm, prefixOfLE, fixedSizeEmbed]
    rw [hfun, ← Measure.map_map (measurable_fixedSizeEmbed m.val) (by fun_prop),
      map_prefixCoordinates_pi P hm]
  have hsource : (Prod.snd : ((Fin n → X) × ℕ) → ℕ) ⁻¹' Set.Iic n =
      ⋃ m : Fin (n + 1),
        (Prod.snd : ((Fin n → X) × ℕ) → ℕ) ⁻¹' ({m.val} : Set ℕ) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · intro hz
      exact ⟨⟨z.2, Nat.lt_succ_of_le hz⟩, rfl⟩
    · rintro ⟨m, hm⟩
      rw [hm]
      exact Nat.le_of_lt_succ m.isLt
  have htarget : (FiniteSample.count : FiniteSample X → ℕ) ⁻¹' Set.Iic n =
      ⋃ m : Fin (n + 1),
        (FiniteSample.count : FiniteSample X → ℕ) ⁻¹' ({m.val} : Set ℕ) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · intro hz
      exact ⟨⟨z.count, Nat.lt_succ_of_le hz⟩, rfl⟩
    · rintro ⟨m, hm⟩
      rw [hm]
      exact Nat.le_of_lt_succ m.isLt
  have hsource_disjoint : Pairwise (Function.onFun Disjoint
      (fun m : Fin (n + 1) ↦
        (Prod.snd : ((Fin n → X) × ℕ) → ℕ) ⁻¹' ({m.val} : Set ℕ))) := by
    intro a b hab
    change Disjoint
      ((Prod.snd : ((Fin n → X) × ℕ) → ℕ) ⁻¹' ({a.val} : Set ℕ))
      ((Prod.snd : ((Fin n → X) × ℕ) → ℕ) ⁻¹' ({b.val} : Set ℕ))
    rw [Set.disjoint_left]
    intro z hza hzb
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hza hzb
    apply hab
    apply Fin.ext
    exact hza.symm.trans hzb
  have htarget_disjoint : Pairwise (Function.onFun Disjoint
      (fun m : Fin (n + 1) ↦
        (FiniteSample.count : FiniteSample X → ℕ) ⁻¹' ({m.val} : Set ℕ))) := by
    intro a b hab
    change Disjoint
      ((FiniteSample.count : FiniteSample X → ℕ) ⁻¹' ({a.val} : Set ℕ))
      ((FiniteSample.count : FiniteSample X → ℕ) ⁻¹' ({b.val} : Set ℕ))
    rw [Set.disjoint_left]
    intro z hza hzb
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hza hzb
    apply hab
    apply Fin.ext
    exact hza.symm.trans hzb
  change Measure.map f (μ.restrict (Prod.snd ⁻¹' Set.Iic n)) =
    ν.restrict (FiniteSample.count ⁻¹' Set.Iic n)
  rw [hsource, Measure.restrict_iUnion hsource_disjoint
    (fun m ↦ measurable_snd (measurableSet_singleton m.val)),
    Measure.map_sum hf.aemeasurable, htarget,
    Measure.restrict_iUnion htarget_disjoint
      (fun m ↦ measurable_finiteSample_count (measurableSet_singleton m.val))]
  congr 1
  funext m
  exact hfiber m

end Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
