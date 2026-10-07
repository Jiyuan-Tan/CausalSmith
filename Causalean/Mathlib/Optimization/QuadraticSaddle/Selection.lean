module
public import Causalean.Mathlib.MeasureTheory.CompactArgminSelection
public import Causalean.Mathlib.Optimization.QuadraticSaddle.Measurability

/-!
# Borel selection for finite quadratic saddle problems

This module derives Borel scalar, weight, and total fallback selections for attained finite
quadratic saddle problems, including ties and degenerate quadratic coefficients.
-/

@[expose] public section

noncomputable section

namespace Causalean.Mathlib.Optimization.QuadraticSaddle

variable {Θ ι κ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
  [Fintype ι] [Fintype κ]

/-- A [quadratic family](hyp:Q), [parameter](hyp:θ), [weight vector](hyp:α), and [scalar
decision](hyp:t) determine the [scalar slope of the weighted objective](goal): the sum over
coordinates of the weight times 2·a·t + b, the derivative of the weighted quadratic objective
in the scalar decision. -/
def Quadratics.slope (Q : Quadratics Θ ι)
    (θ : Θ) (α : EuclideanSpace ℝ ι) (t : ℝ) : ℝ :=
  ∑ i, α i * (2 * Q.a i θ * t + Q.b i θ)

/-- A [quadratic family](hyp:Q) has a [jointly Borel scalar slope](goal) in the parameter,
finite weights, and scalar decision. -/
theorem Quadratics.measurable_slope (Q : Quadratics Θ ι) :
    Measurable (fun x : Θ × (EuclideanSpace ℝ ι × ℝ) =>
      Q.slope x.1 x.2.1 x.2.2) := by
  unfold Quadratics.slope
  apply Finset.measurable_sum
  intro i hi
  have hθ : Measurable (fun x : Θ × (EuclideanSpace ℝ ι × ℝ) => x.1) :=
    measurable_fst
  have hα : Measurable (fun x : Θ × (EuclideanSpace ℝ ι × ℝ) => x.2.1 i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable.comp
      (measurable_fst.comp measurable_snd)
  have ht : Measurable (fun x : Θ × (EuclideanSpace ℝ ι × ℝ) => x.2.2) :=
    measurable_snd.comp measurable_snd
  exact hα.mul ((((measurable_const.mul ((Q.measurable_a i).comp hθ)).mul ht)).add
    ((Q.measurable_b i).comp hθ))

/-- A [quadratic family](hyp:Q), [parameter](hyp:θ), and [scalar decision](hyp:t) have a
[scalar slope continuous in the weight vector](goal). -/
theorem Quadratics.continuous_slope_weight (Q : Quadratics Θ ι)
    (θ : Θ) (t : ℝ) : Continuous (fun α : EuclideanSpace ℝ ι => Q.slope θ α t) := by
  unfold Quadratics.slope
  fun_prop

/-- A [quadratic family](hyp:Q), [parameter](hyp:θ), [weight vector](hyp:α), and [scalar
decision](hyp:t) with a [global scalar minimum](hyp:hmin) have [zero scalar slope](goal). -/
theorem Quadratics.slope_eq_zero_of_global_min (Q : Quadratics Θ ι)
    (θ : Θ) (α : EuclideanSpace ℝ ι) (t : ℝ)
    (hmin : ∀ u : ℝ, Q.objective θ α t ≤ Q.objective θ α u) :
    Q.slope θ α t = 0 := by
  have hd : HasDerivAt (fun u => Q.objective θ α u) (Q.slope θ α t) t := by
    unfold Quadratics.objective Quadratics.slope
    apply HasDerivAt.fun_sum
    intro i hi
    convert (((((hasDerivAt_id t).pow 2).const_mul (Q.a i θ)).add
      ((hasDerivAt_id t).const_mul (Q.b i θ))).add_const (Q.c i θ)).const_mul
        (α i) using 1 <;> first | rfl | (simp only [id_eq, Nat.reduceSub, pow_one]; ring)
  have hm : IsLocalMin (fun u => Q.objective θ α u) t :=
    isLocalMinOn_univ_iff.mp (((isMinOn_univ_iff).2 hmin).localize)
  exact hm.hasDerivAt_eq_zero hd

/-- A [fixed polytope](hyp:P), [quadratic family](hyp:Q), [parameter](hyp:θ), [weight
vector](hyp:α), and [scalar decision](hyp:t) with [feasible nonnegative weights](hyp:hα) and
[zero scalar slope](hyp:hz) have a [global scalar minimum](goal), including degenerate
quadratic coefficients. -/
theorem Quadratics.global_min_of_slope_eq_zero (P : Polytope ι κ)
    (Q : Quadratics Θ ι) (θ : Θ) (α : EuclideanSpace ℝ ι) (t : ℝ)
    (hα : α ∈ P.weights) (hz : Q.slope θ α t = 0) :
    ∀ u : ℝ, Q.objective θ α t ≤ Q.objective θ α u := by
  intro u
  have hcoef : 0 ≤ ∑ i, α i * Q.a i θ := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hα.1 i) (Q.nonneg_a θ i)
  have hdiff : Q.objective θ α u - Q.objective θ α t =
      (u - t) ^ 2 * (∑ i, α i * Q.a i θ) +
        (u - t) * Q.slope θ α t := by
    calc
      Q.objective θ α u - Q.objective θ α t =
          ∑ i, (α i * (Q.a i θ * u ^ 2 + Q.b i θ * u + Q.c i θ) -
            α i * (Q.a i θ * t ^ 2 + Q.b i θ * t + Q.c i θ)) := by
              simp [Quadratics.objective, Finset.sum_sub_distrib]
      _ = ∑ i, ((u - t) ^ 2 * (α i * Q.a i θ) +
            (u - t) * (α i * (2 * Q.a i θ * t + Q.b i θ))) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = (u - t) ^ 2 * (∑ i, α i * Q.a i θ) +
            (u - t) * Q.slope θ α t := by
              simp only [Quadratics.slope, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hz, mul_zero, add_zero] at hdiff
  nlinarith [sq_nonneg (u - t), mul_nonneg (sq_nonneg (u - t)) hcoef]

set_option maxHeartbeats 800000 in
/-- A [fixed polytope](hyp:P), [quadratic family](hyp:Q), [Borel parameter domain](hyp:D,hD),
and [pointwise saddle-attainment certificate](hyp:hAttains) have a [Borel scalar decision that
minimizes the maximum envelope and attains the max-min value](goal). -/
theorem exists_measurable_envelope_minimizer_on
    (P : Polytope ι κ) (Q : Quadratics Θ ι)
    (D : Set Θ) (hD : MeasurableSet D)
    (hAttains : ∀ θ ∈ D, ∃ α t, IsSaddle P Q θ α t) :
    ∃ t : D → ℝ, Measurable t ∧
      ∀ θ : D, Q.envelope P θ.1 (t θ) = value P Q θ.1 := by
  classical
  letI : StandardBorelSpace D := hD.standardBorel
  let K : ℕ → Set (EuclideanSpace ℝ (Fin 1)) :=
    fun n => Metric.closedBall 0 (n : ℝ)
  have hK (n : ℕ) : IsCompact (K n) := isCompact_closedBall _ _
  have hKne (n : ℕ) : (K n).Nonempty :=
    ⟨0, Metric.mem_closedBall_self (by positivity)⟩
  let f : D × EuclideanSpace ℝ (Fin 1) → ℝ :=
    fun x => Q.envelope P x.1.1 (x.2 0)
  have hf : Measurable f := by
    change Measurable ((fun z : Θ × ℝ => Q.envelope P z.1 z.2) ∘
      (fun x : D × EuclideanSpace ℝ (Fin 1) => (x.1.1, x.2 0)))
    have hcoord : Measurable (fun y : EuclideanSpace ℝ (Fin 1) => y 0) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).measurable
    have hpair : Measurable (fun x : D × EuclideanSpace ℝ (Fin 1) =>
        ((x.1.1, x.2 0) : Θ × ℝ)) :=
      (measurable_subtype_coe.comp measurable_fst).prodMk
        (hcoord.comp measurable_snd)
    exact (Q.measurable_envelope P).comp hpair
  have hfc' (n : ℕ) (x : D) : ContinuousOn (fun y => f (x, y)) (K n) := by
    exact (Q.continuous_envelope P x.1).comp
      (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0) |>.continuousOn
  have hsel (n : ℕ) : ∃ π : D → EuclideanSpace ℝ (Fin 1),
      Measurable π ∧ ∀ x, π x ∈ K n ∧ ∀ y ∈ K n, f (x, π x) ≤ f (x, y) :=
    Causalean.Mathlib.MeasureTheory.borelMeasurable_compact_argmin_selector
      (K n) (hK n) (hKne n) f hf (hfc' n)
  choose π hπm hπ using hsel
  let v : D → ℝ := fun x => value P Q x.1
  let g : ℕ → D → ℝ := fun n x => (π n x) 0
  have hg (n : ℕ) : Measurable (g n) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).measurable.comp (hπm n)
  have hfg (n : ℕ) : Measurable (fun x : D => Q.envelope P x.1 (g n x)) := by
    change Measurable ((fun z : Θ × ℝ => Q.envelope P z.1 z.2) ∘
      (fun x : D => (x.1, g n x)))
    exact (Q.measurable_envelope P).comp
      (measurable_subtype_coe.prodMk (hg n))
  have hv : Measurable v := measurable_value_on P Q D hAttains
  let p : D → ℕ → Prop := fun x n => Q.envelope P x.1 (g n x) = v x
  have hpmeas (n : ℕ) : MeasurableSet {x : D | p x n} := by
    change MeasurableSet {x : D | Q.envelope P x.1 (g n x) = v x}
    exact measurableSet_eq_fun (hfg n) hv
  have hmin (x : D) (s : ℝ) (hs : ∃ α, IsSaddle P Q x.1 α s) :
      ∀ t, v x ≤ Q.envelope P x.1 t := by
    obtain ⟨α, hα⟩ := hs
    intro t
    calc
      v x = Q.objective x.1 α s := value_eq_of_isSaddle P Q x.1 α s hα
      _ ≤ Q.objective x.1 α t := hα.2.1 t
      _ ≤ Q.envelope P x.1 t := Q.objective_le_envelope P x.1 t α hα.1
  have hp (x : D) : ∃ n, p x n := by
    obtain ⟨α, s, hs⟩ := hAttains x.1 x.2
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖s‖ ≤ (n : ℝ) :=
      exists_nat_ge ‖s‖
    have hsingle : EuclideanSpace.single (0 : Fin 1) s ∈ K n := by
      simpa [K, Metric.mem_closedBall, dist_zero_right,
        EuclideanSpace.norm_single] using hn
    have heval : (EuclideanSpace.single (0 : Fin 1) s) 0 = s := by simp
    refine ⟨n, ?_⟩
    have hle := (hπ n x).2 (EuclideanSpace.single 0 s) hsingle
    have hlow := hmin x s ⟨α, hs⟩ (g n x)
    have hval : Q.envelope P x.1 s = v x := by
      rw [Q.envelope_eq_of_isSaddle P x.1 α s hs,
        ← value_eq_of_isSaddle P Q x.1 α s hs]
    exact le_antisymm (by simpa [f, g, heval, hval] using hle) hlow
  let n : D → ℕ := fun x => Nat.find (hp x)
  have hn : Measurable n := measurable_find hp hpmeas
  refine ⟨fun x => g (n x) x, ?_, ?_⟩
  · have hge : Measurable (fun z : D × ℕ => g z.2 z.1) :=
      measurable_from_prod_countable_left (fun k => hg k)
    exact hge.comp (measurable_id.prodMk hn)
  · intro x
    exact Nat.find_spec (hp x)

/-- A [fixed polytope](hyp:P), [quadratic family](hyp:Q), [Borel parameter domain](hyp:D,hD),
[pointwise saddle-attainment certificate](hyp:hAttains), [Borel scalar decision](hyp:t,ht), and
[envelope-value identity](hyp:hEq) have a [Borel feasible weight forming a saddle with that
decision](goal). -/
theorem exists_measurable_saddle_weight_on
    (P : Polytope ι κ) (Q : Quadratics Θ ι)
    (D : Set Θ) (hD : MeasurableSet D)
    (hAttains : ∀ θ ∈ D, ∃ α t, IsSaddle P Q θ α t)
    (t : D → ℝ) (ht : Measurable t)
    (hEq : ∀ θ : D, Q.envelope P θ.1 (t θ) = value P Q θ.1) :
    ∃ α : D → EuclideanSpace ℝ ι, Measurable α ∧
      ∀ θ : D, IsSaddle P Q θ.1 (α θ) (t θ) := by
  classical
  haveI : StandardBorelSpace D := hD.standardBorel
  let f : D × EuclideanSpace ℝ ι → ℝ := fun x =>
    |Q.objective x.1.1 x.2 (t x.1) - value P Q x.1.1| +
      |Q.slope x.1.1 x.2 (t x.1)|
  have harg : Measurable (fun x : D × EuclideanSpace ℝ ι =>
      ((x.1.1, (x.2, t x.1)) : Θ × (EuclideanSpace ℝ ι × ℝ))) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk
      (measurable_snd.prodMk (ht.comp measurable_fst))
  have hv : Measurable (fun x : D × EuclideanSpace ℝ ι => value P Q x.1.1) :=
    (measurable_value_on P Q D hAttains).comp measurable_fst
  have hf : Measurable f :=
    ((Q.measurable_objective.comp harg).sub hv).abs.add
      ((Q.measurable_slope.comp harg).abs)
  have hfc (x : D) : ContinuousOn (fun α => f (x, α)) P.weights := by
    have ho : Continuous (fun α : EuclideanSpace ℝ ι =>
        Q.objective x.1 α (t x)) := by
      unfold Quadratics.objective
      fun_prop
    have hs := Q.continuous_slope_weight x.1 (t x)
    convert ((ho.sub (continuous_const : Continuous
        (fun _ : EuclideanSpace ℝ ι => value P Q x.1))).abs.add hs.abs).continuousOn using 1
    ext α
    rfl
  obtain ⟨α, hαm, hαmin⟩ :=
    Causalean.Mathlib.MeasureTheory.borelMeasurable_compact_argmin_selector
      P.weights P.compact P.nonempty f hf hfc
  refine ⟨α, hαm, ?_⟩
  intro x
  obtain ⟨β, s, hβs⟩ := hAttains x.1 x.2
  have hβt : IsSaddle P Q x.1 β (t x) := by
    apply Q.isSaddle_at_envelope_le P x.1 β s (t x) hβs
    rw [hEq x, Q.envelope_eq_of_isSaddle P x.1 β s hβs]
    exact (value_eq_of_isSaddle P Q x.1 β s hβs).le
  have hβval : Q.objective x.1 β (t x) = value P Q x.1 :=
    (value_eq_of_isSaddle P Q x.1 β (t x) hβt).symm
  have hβslope : Q.slope x.1 β (t x) = 0 :=
    Q.slope_eq_zero_of_global_min x.1 β (t x) hβt.2.1
  have hfβ : f (x, β) = 0 := by simp [f, hβval, hβslope]
  have hfα : f (x, α x) = 0 := by
    have hle := (hαmin x).2 β hβt.1
    have hnonneg : 0 ≤ f (x, α x) := add_nonneg (abs_nonneg _) (abs_nonneg _)
    rw [hfβ] at hle
    exact le_antisymm hle hnonneg
  have hzero : Q.objective x.1 (α x) (t x) = value P Q x.1 ∧
      Q.slope x.1 (α x) (t x) = 0 := by
    have hp : |Q.objective x.1 (α x) (t x) - value P Q x.1| = 0 ∧
        |Q.slope x.1 (α x) (t x)| = 0 :=
      (add_eq_zero_iff_of_nonneg (abs_nonneg _) (abs_nonneg _)).mp hfα
    exact ⟨sub_eq_zero.mp (abs_eq_zero.mp hp.1), abs_eq_zero.mp hp.2⟩
  refine ⟨(hαmin x).1,
    Q.global_min_of_slope_eq_zero P x.1 (α x) (t x) (hαmin x).1 hzero.2, ?_⟩
  intro γ hγ
  calc
    Q.objective x.1 γ (t x) ≤ Q.envelope P x.1 (t x) :=
      Q.objective_le_envelope P x.1 (t x) γ hγ
    _ = value P Q x.1 := hEq x
    _ = Q.objective x.1 (α x) (t x) := hzero.1.symm

/-- A [fixed polytope](hyp:P), [quadratic family](hyp:Q), [Borel parameter domain](hyp:D,hD),
and [pointwise saddle-attainment certificate](hyp:hAttains) have [Borel saddle weights and
scalar decisions on that domain](goal). -/
theorem exists_measurable_saddle_on
    (P : Polytope ι κ) (Q : Quadratics Θ ι)
    (D : Set Θ) (hD : MeasurableSet D)
    (hAttains : ∀ θ ∈ D, ∃ α t, IsSaddle P Q θ α t) :
    ∃ α : D → EuclideanSpace ℝ ι, ∃ t : D → ℝ,
      Measurable α ∧ Measurable t ∧
      ∀ θ : D, IsSaddle P Q θ.1 (α θ) (t θ) := by
  obtain ⟨t, ht, hEq⟩ :=
    exists_measurable_envelope_minimizer_on P Q D hD hAttains
  obtain ⟨α, hα, hs⟩ :=
    exists_measurable_saddle_weight_on P Q D hD hAttains t ht hEq
  exact ⟨α, t, hα, ht, hs⟩

/-- A [fixed polytope](hyp:P), [quadratic family](hyp:Q), [Borel parameter domain](hyp:D,hD),
[pointwise saddle-attainment certificate](hyp:hAttains), and [fallback triple](hyp:fallback)
have a [total Borel policy that equals the fallback off the domain and returns a saddle and its
max-min value on the domain](goal). -/
theorem exists_measurable_saddle_with_fallback
    (P : Polytope ι κ) (Q : Quadratics Θ ι)
    (D : Set Θ) (hD : MeasurableSet D)
    (hAttains : ∀ θ ∈ D, ∃ α t, IsSaddle P Q θ α t)
    (fallback : EuclideanSpace ℝ ι × ℝ × ℝ) :
    ∃ policy : Θ → EuclideanSpace ℝ ι × ℝ × ℝ,
      Measurable policy ∧
      (∀ θ ∉ D, policy θ = fallback) ∧
      (∀ θ ∈ D,
        IsSaddle P Q θ (policy θ).1 (policy θ).2.1 ∧
        (policy θ).2.2 = Q.objective θ (policy θ).1 (policy θ).2.1 ∧
        (policy θ).2.2 = value P Q θ) := by
  classical
  obtain ⟨α, t, hα, ht, hs⟩ := exists_measurable_saddle_on P Q D hD hAttains
  let policy : Θ → EuclideanSpace ℝ ι × ℝ × ℝ := fun θ =>
    if hθ : θ ∈ D then (α ⟨θ, hθ⟩, t ⟨θ, hθ⟩, value P Q θ)
    else fallback
  have hv : Measurable (fun θ : D => value P Q θ.1) :=
    measurable_value_on P Q D hAttains
  have hp : Measurable policy := by
    change Measurable (fun θ : Θ =>
      if hθ : θ ∈ D then (α ⟨θ, hθ⟩, t ⟨θ, hθ⟩, value P Q θ)
      else fallback)
    exact Measurable.dite (hα.prodMk (ht.prodMk hv)) measurable_const hD
  refine ⟨policy, hp, ?_, ?_⟩
  · intro θ hθ
    simp [policy, hθ]
  · intro θ hθ
    have h := hs (⟨θ, hθ⟩ : D)
    have heq := value_eq_of_isSaddle P Q θ (α ⟨θ, hθ⟩) (t ⟨θ, hθ⟩) h
    simpa [policy, hθ] using And.intro h heq

end Causalean.Mathlib.Optimization.QuadraticSaddle
