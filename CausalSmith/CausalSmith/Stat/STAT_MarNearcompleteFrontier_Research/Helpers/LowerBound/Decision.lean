module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.OneCell
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.Converse.Target
public import Causalean.Stat.Minimax.LeCamTwoPoint
public import Causalean.Stat.Minimax.MinimaxRisk

/-! # Decision theoretic reductions for the one cell lower bound -/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory

-- @node: parametric_point_pair_lower
/-- A hard separated pair gives a uniform squared risk lower bound. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `u`](hyp:u), [the specified input `P₀`](hyp:P₀), [the specified input `P₁`](hyp:P₁), [the specified input `hu`](hyp:hu), [the specified input `htau₀`](hyp:htau₀), [the specified input `htau₁`](hyp:htau₁), [the stated mathematical conclusion holds](goal). Given [the specified input `htv`](hyp:htv). -/
lemma parametric_point_pair_lower {n d : ℕ} {q u : ℝ}
    (P₀ P₁ : ClassLaw d q) (hu : 0 < u)
    (htau₀ : tau P₀.val = 1 / 2) (htau₁ : tau P₁.val = 1 / 2 + u)
    (htv : Causalean.Stat.tvDist (samplePi P₁.val n) (samplePi P₀.val n) ≤ 1 / 2) :
    u ^ 2 / 16 ≤ pointMinimaxRisk n d q := by
  letI : Nonempty (Estimator n d) :=
    ⟨⟨fun _ => 0, measurable_const, fun _ => by constructor <;> norm_num⟩⟩
  unfold pointMinimaxRisk
  refine le_ciInf fun T => ?_
  letI : IsProbabilityMeasure (samplePi P₀.val n) := by unfold samplePi; infer_instance
  letI : IsProbabilityMeasure (samplePi P₁.val n) := by unfold samplePi; infer_instance
  have hprob := Causalean.Stat.two_point_lower_bound_of_tvDist_le
    (P₀ := samplePi P₀.val n) (P₁ := samplePi P₁.val n)
    T.measurable (s := u / 2) (c := 1 / 2)
    (θ₀ := tau P₀.val) (θ₁ := tau P₁.val)
    (by rw [htau₀, htau₁]; simp [abs_of_pos hu]; linarith)
    (by simpa [Causalean.Stat.tvDist_symm] using htv)
  have hrisk (P : ClassLaw d q) :
      (u / 2) ^ 2 * (samplePi P.val n).real
          {o | u / 2 ≤ |T o - tau P.val|} ≤
        ∫ o, (T o - tau P.val) ^ 2 ∂samplePi P.val n := by
    letI : IsProbabilityMeasure (samplePi P.val n) := by unfold samplePi; infer_instance
    have hset : {o | u / 2 ≤ |T o - tau P.val|} =
        {o | (u / 2) ^ 2 ≤ (T o - tau P.val) ^ 2} := by
      ext o
      simp only [Set.mem_setOf_eq]
      rw [sq_le_sq, abs_of_pos (half_pos hu)]
    rw [hset]
    exact mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun o => sq_nonneg (T o - tau P.val))
      (μ := samplePi P.val n) Integrable.of_finite ((u / 2) ^ 2)
  have hpair : u ^ 2 / 16 ≤ max
      (∫ o, (T o - tau P₀.val) ^ 2 ∂samplePi P₀.val n)
      (∫ o, (T o - tau P₁.val) ^ 2 ∂samplePi P₁.val n) := by
    have h0 := hrisk P₀
    have h1 := hrisk P₁
    by_cases hle :
        (samplePi P₀.val n).real {o | u / 2 ≤ |T o - tau P₀.val|} ≤
          (samplePi P₁.val n).real {o | u / 2 ≤ |T o - tau P₁.val|}
    · rw [max_eq_right hle] at hprob
      calc
        u ^ 2 / 16 ≤ (u / 2) ^ 2 *
            (samplePi P₁.val n).real {o | u / 2 ≤ |T o - tau P₁.val|} := by
              nlinarith [sq_nonneg u]
        _ ≤ _ := h1.trans (le_max_right _ _)
    · have hle' := le_of_not_ge hle
      rw [max_eq_left hle'] at hprob
      calc
        u ^ 2 / 16 ≤ (u / 2) ^ 2 *
            (samplePi P₀.val n).real {o | u / 2 ≤ |T o - tau P₀.val|} := by
              nlinarith [sq_nonneg u]
        _ ≤ _ := h0.trans (le_max_left _ _)
  have hb : BddAbove (Set.range fun P : ClassLaw d q =>
      ∫ o, (T o - tau P.val) ^ 2 ∂samplePi P.val n) := by
    refine ⟨4, ?_⟩
    rintro z ⟨P, rfl⟩
    haveI : IsProbabilityMeasure (samplePi P.val n) := by unfold samplePi; infer_instance
    have hrange (o : Fin n → Obs d) : (T o - tau P.val) ^ 2 ≤ 4 := by
      rcases T.range o with ⟨hT0, hT1⟩
      rcases tau_range P.val with ⟨hτ0, hτ1⟩
      nlinarith [sq_nonneg (T o + 1), sq_nonneg (1 - T o),
        sq_nonneg (tau P.val + 1), sq_nonneg (1 - tau P.val)]
    have hInt : Integrable (fun o : Fin n → Obs d =>
        (T o - tau P.val) ^ 2) (samplePi P.val n) := Integrable.of_finite
    simpa using (integral_mono hInt (integrable_const 4) hrange)
  exact hpair.trans (max_le (le_ciSup hb P₀) (le_ciSup hb P₁))

-- @node: parametric_length_lower_of_law
/-- A fixed legal law transfers a length lower bound through the minimax extrema. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `c`](hyp:c), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). Given [the specified input `α`](hyp:α), [the specified input `hα`](hyp:hα). Given [the specified input `h`](hyp:h). -/
lemma parametric_length_lower_of_law {n d : ℕ} {q α c : ℝ}
    (P : ClassLaw d q) (hα : 0 ≤ α)
    (h : ∀ I : HonestIntervalClass n d q α,
      c ≤ ∫ o, (I.val.hi o - I.val.lo o) ∂samplePi P.val n) :
    c ≤ lengthMinimaxRisk n d q α := by
  let Iall : IntervalProc n d :=
    ⟨fun _ => -1, fun _ => 1, measurable_const, measurable_const,
      fun _ => by constructor <;> norm_num⟩
  letI : Nonempty (HonestIntervalClass n d q α) :=
    ⟨⟨Iall, fun P' => by
      haveI : IsProbabilityMeasure (samplePi P'.val n) := by unfold samplePi; infer_instance
      have hevent : {o : Fin n → Obs d |
          tau P'.val ∈ Set.Icc (Iall.lo o) (Iall.hi o)} = Set.univ := by
        ext o
        simp [Iall, tau_range P'.val]
      rw [hevent, probReal_univ]
      linarith⟩⟩
  unfold lengthMinimaxRisk
  refine le_ciInf fun I => ?_
  have hb : BddAbove (Set.range fun P' : ClassLaw d q =>
      ∫ o, (I.val.hi o - I.val.lo o) ∂samplePi P'.val n) := by
    refine ⟨2, ?_⟩
    rintro z ⟨P', rfl⟩
    haveI : IsProbabilityMeasure (samplePi P'.val n) := by unfold samplePi; infer_instance
    have hrange (o : Fin n → Obs d) : I.val.hi o - I.val.lo o ≤ 2 := by
      rcases I.val.bounds o with ⟨hlo, _, hhi⟩
      linarith
    have hInt : Integrable (fun o => I.val.hi o - I.val.lo o)
        (samplePi P'.val n) := Integrable.of_finite
    simpa using (integral_mono hInt (integrable_const 2) hrange)
  exact (h I).trans (le_ciSup hb P)

-- @node: parametric_interval_pair_lower
/-- Coverage under a TV close pair forces expected interval length. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `u`](hyp:u), [the specified input `P₀`](hyp:P₀), [the specified input `P₁`](hyp:P₁), [the specified input `hu`](hyp:hu), [the specified input `htau₀`](hyp:htau₀), [the specified input `htau₁`](hyp:htau₁), [the stated mathematical conclusion holds](goal). Given [the specified input `α`](hyp:α), [the specified input `hα`](hyp:hα). Given [the specified input `htv`](hyp:htv). -/
lemma parametric_interval_pair_lower {n d : ℕ} {q α u : ℝ}
    (P₀ P₁ : ClassLaw d q) (hu : 0 < u) (hα : 0 ≤ α)
    (htau₀ : tau P₀.val = 1 / 2) (htau₁ : tau P₁.val = 1 / 2 + u)
    (htv : Causalean.Stat.tvDist (samplePi P₀.val n) (samplePi P₁.val n) ≤
      (1 - 2 * α) / 2) :
    u * (1 - 2 * α) / 2 ≤ lengthMinimaxRisk n d q α := by
  apply parametric_length_lower_of_law P₀ hα
  intro I
  let μ₀ := samplePi P₀.val n
  let μ₁ := samplePi P₁.val n
  let E₀ := {o | tau P₀.val ∈ Set.Icc (I.val.lo o) (I.val.hi o)}
  let E₁ := {o | tau P₁.val ∈ Set.Icc (I.val.lo o) (I.val.hi o)}
  haveI : IsProbabilityMeasure μ₀ := by dsimp [μ₀]; unfold samplePi; infer_instance
  haveI : IsProbabilityMeasure μ₁ := by dsimp [μ₁]; unfold samplePi; infer_instance
  have hE₀ : MeasurableSet E₀ := Set.toFinite E₀ |>.measurableSet
  have hE₁ : MeasurableSet E₁ := Set.toFinite E₁ |>.measurableSet
  have hcov₀ : 1 - α ≤ μ₀.real E₀ := I.property P₀
  have hcov₁ : 1 - α ≤ μ₁.real E₁ := I.property P₁
  have htvE := Causalean.Stat.abs_measureReal_sub_le_tvDist
    (μ := μ₀) (ν := μ₁) hE₁
  have htransfer : 1 - α - (1 - 2 * α) / 2 ≤ μ₀.real E₁ := by
    have hd := (abs_le.mp htvE).1
    dsimp [μ₀, μ₁] at hd
    linarith
  have hinter : (1 - 2 * α) / 2 ≤ μ₀.real (E₀ ∩ E₁) := by
    have hc₀ : μ₀.real E₀ᶜ ≤ α := by
      rw [probReal_compl_eq_one_sub hE₀]
      linarith
    have hc₁ : μ₀.real E₁ᶜ ≤ α + (1 - 2 * α) / 2 := by
      rw [probReal_compl_eq_one_sub hE₁]
      linarith
    have hu' := measureReal_union_le (μ := μ₀) E₀ᶜ E₁ᶜ
    have heq : E₀ ∩ E₁ = (E₀ᶜ ∪ E₁ᶜ)ᶜ := by ext o; simp
    rw [heq, probReal_compl_eq_one_sub (hE₀.compl.union hE₁.compl)]
    linarith
  have hsubset : E₀ ∩ E₁ ⊆ {o | u ≤ I.val.hi o - I.val.lo o} := by
    intro o ho
    change (tau P₀.val ∈ Set.Icc (I.val.lo o) (I.val.hi o)) ∧
      (tau P₁.val ∈ Set.Icc (I.val.lo o) (I.val.hi o)) at ho
    rcases ho with ⟨⟨hlo₀, hhi₀⟩, ⟨hlo₁, hhi₁⟩⟩
    rw [htau₀] at hlo₀ hhi₀
    rw [htau₁] at hlo₁ hhi₁
    change u ≤ I.val.hi o - I.val.lo o
    linarith only [hlo₀, hhi₁]
  have hmass : μ₀.real (E₀ ∩ E₁) ≤
      μ₀.real {o | u ≤ I.val.hi o - I.val.lo o} := measureReal_mono hsubset
  have hthreshold : u * μ₀.real {o | u ≤ I.val.hi o - I.val.lo o} ≤
      ∫ o, (I.val.hi o - I.val.lo o) ∂μ₀ := by
    exact mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun o => sub_nonneg.mpr (I.val.bounds o).2.1)
      (μ := μ₀) Integrable.of_finite u
  calc
    u * (1 - 2 * α) / 2 ≤ u * μ₀.real (E₀ ∩ E₁) := by
      nlinarith [mul_le_mul_of_nonneg_left hinter (le_of_lt hu)]
    _ ≤ u * μ₀.real {o | u ≤ I.val.hi o - I.val.lo o} :=
      mul_le_mul_of_nonneg_left hmass (le_of_lt hu)
    _ ≤ _ := hthreshold

end CausalSmith.Stat.MarNearcompleteFrontier
