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
