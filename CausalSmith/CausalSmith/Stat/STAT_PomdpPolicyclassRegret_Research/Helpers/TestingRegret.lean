module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.FanoGate
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorExpectation

/-! # Testing reductions for the common-kernel lower bound

A separated optimal policy charges each wrong output its value gap. Averaging
these losses and restricting the model class gives the minimax reduction in
(43)--(49), without assuming any information bound or testing conclusion.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators

/-- A wrong output pays the separation from the distinguished policy. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the model](hyp:m),
[the codeword index](hyp:v), [the candidate index](hyp:j), [the value gap](hyp:gap),
[the value gap assumption](hyp:hgap), and [the candidate index assumption](hyp:hj), this
establishes [the testing simple regret gap result](goal). -/
-- @node: testing_simpleRegret_gap
lemma testing_simpleRegret_gap {T M : Nat} (m : ModelIndex T M)
    (v j : Fin M) (gap : ℝ) (hgap : ∀ w, w ≠ v →
      gap ≤ policyValue m v - policyValue m w) (hj : j ≠ v) :
    gap ≤ simpleRegret m j := by
  have hbest := le_ciSup (Finite.bddAbove_range (policyValue m)) v
  exact (hgap j hj).trans (sub_le_sub_right hbest _)

/-- Integrating the wrong-output indicator gives the expected testing loss. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the observable selector](hyp:sel), [the model](hyp:m), [the class assumption](hyp:hClass),
[the codeword index](hyp:v), [the value gap](hyp:gap), and [the value gap assumption](hyp:hgap),
this establishes [the testing expected regret gap result](goal). -/
-- @node: testing_expectedRegret_gap
lemma testing_expectedRegret_gap {T M : Nat} (t0 zeta C : ℝ)
    (sel : ObservableSelector T M) (m : ModelIndex T M)
    (hClass : PolicyListClass t0 zeta C m) (v : Fin M) (gap : ℝ)
    (hgap : ∀ w, w ≠ v → gap ≤ policyValue m v - policyValue m w) :
    gap * (obsLaw m.Mx.toRawB).real
      {w | sel.1 m.nX m.Mx.b m.Mx.E w ≠ v} ≤ expectedRegret sel m := by
  classical
  let μ := obsLaw m.Mx.toRawB
  let : IsProbabilityMeasure μ := by
    dsimp [μ, obsLaw]
    have hobs : Measurable (@obsProj T m.nX m.nH) := by fun_prop
    exact Measure.isProbabilityMeasure_map hobs.aemeasurable
  let bad := {w | sel.1 m.nX m.Mx.b m.Mx.E w ≠ v}
  have hbad : MeasurableSet bad := by
    exact (measurableSet_eq_fun (sel.2 m.nX m.Mx.b m.Mx.E) measurable_const).compl
  have hle : ∀ w, bad.indicator (fun _ ↦ gap) w ≤
      simpleRegret m (sel.1 m.nX m.Mx.b m.Mx.E w) := by
    intro w
    by_cases hw : w ∈ bad
    · rw [Set.indicator_of_mem hw]
      exact testing_simpleRegret_gap m v _ gap hgap hw
    · rw [Set.indicator_of_notMem hw]
      exact (selector_simpleRegret_unit t0 zeta C m hClass _).1
  have hint := integral_mono ((integrable_const gap).indicator hbad)
    (selector_simpleRegret_integrable t0 zeta C sel m hClass) hle
  rw [integral_indicator_const gap hbad] at hint
  simpa only [smul_eq_mul, mul_comm, bad, expectedRegret] using hint

/-- The optimal average testing error is no greater than any measurable test's error. For
[the sample space](hyp:Ω), [the candidate-policy count](hyp:M), [the probability law](hyp:P),
[the ψ](hyp:ψ), and [the ψ assumption](hyp:hψ), this establishes
[the testing fano average error bound result](goal). -/
-- @node: testing_fanoAverageError_le
lemma testing_fanoAverageError_le {Ω : Type*} [MeasurableSpace Ω]
    (M : Nat) (P : Fin M → Measure Ω) (ψ : Ω → Fin M) (hψ : Measurable ψ) :
    fanoAverageError M P ≤
      (M : ℝ)⁻¹ * ∑ v, (P v).real {w | ψ w ≠ v} := by
  apply ciInf_le (f := fun ψ : {ψ : Ω → Fin M // Measurable ψ} ↦
    (M : ℝ)⁻¹ * ∑ v, (P v).real {w | ψ.1 w ≠ v}) ?_ ⟨ψ, hψ⟩
  refine ⟨0, ?_⟩
  rintro _ ⟨ψ, rfl⟩
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun v _ ↦ measureReal_nonneg)

/-- Any lower risk witnessed inside the class transfers to its minimax value. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the candidate-policy count assumption](hyp:hM), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the c](hyp:c), and
[the stated assumption](hyp:h), this establishes
[the testing bound minimax regret result](goal). -/
-- @node: testing_le_minimaxRegret
lemma testing_le_minimaxRegret {T M : Nat} (hM : 2 ≤ M) (t0 zeta C c : ℝ)
    (h : ∀ sel : ObservableSelector T M, ∃ m : ModelIndex T M,
      PolicyListClass t0 zeta C m ∧ c ≤ expectedRegret sel m) :
    c ≤ minimaxRegret T M t0 zeta C := by
  let : Nonempty (ObservableSelector T M) :=
    ⟨⟨fun _ _ _ _ ↦ ⟨0, by omega⟩, fun _ _ _ ↦ measurable_const⟩⟩
  apply Causalean.Stat.le_minimaxValue
  intro sel
  obtain ⟨m, hm, hc⟩ := h sel
  apply hc.trans
  refine Causalean.Stat.le_worstCaseRisk
    (risk := fun (sel : ObservableSelector T M)
      (m : {m : ModelIndex T M // PolicyListClass t0 zeta C m}) ↦
        expectedRegret sel m.1) ?_ ⟨m, hm⟩
  refine ⟨1, ?_⟩
  rintro _ ⟨m', rfl⟩
  exact (selector_expectedRegret_unit t0 zeta C sel m'.1 m'.2).2

/-- An average lower bound supplies a worst alternative, then a minimax bound. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the candidate-policy count assumption](hyp:hM), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the c](hyp:c),
[the models](hyp:models), [the class assumption](hyp:hClass), and
[the avg assumption](hyp:havg), this establishes
[the testing average bound minimax regret result](goal). -/
-- @node: testing_average_le_minimaxRegret
lemma testing_average_le_minimaxRegret {T M : Nat} (hM : 2 ≤ M)
    (t0 zeta C c : ℝ) (models : Fin M → ModelIndex T M)
    (hClass : ∀ v, PolicyListClass t0 zeta C (models v))
    (havg : ∀ sel : ObservableSelector T M,
      c ≤ (M : ℝ)⁻¹ * ∑ v, expectedRegret sel (models v)) :
    c ≤ minimaxRegret T M t0 zeta C := by
  classical
  let : Nonempty (Fin M) := ⟨⟨0, by omega⟩⟩
  apply testing_le_minimaxRegret hM t0 zeta C c
  intro sel
  have hpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  by_contra h
  have hall : ∀ v, expectedRegret sel (models v) < c := by
    intro v
    by_contra hv
    exact h ⟨models v, hClass v, le_of_not_gt hv⟩
  have hsum : (∑ v, expectedRegret sel (models v)) < (M : ℝ) * c := by
    have := Finset.sum_lt_sum_of_nonempty
      (s := Finset.univ) (f := fun v ↦ expectedRegret sel (models v))
      (g := fun _ ↦ c) (by exact Finset.univ_nonempty) (fun v _ ↦ hall v)
    simpa using this
  have hlt := mul_lt_mul_of_pos_left hsum (inv_pos.mpr hpos)
  have hid : (M : ℝ)⁻¹ * ((M : ℝ) * c) = c := by field_simp
  rw [hid] at hlt
  exact (not_lt_of_ge (havg sel)) hlt

/-- A uniform average testing-error bound transfers through a policy gap to minimax regret. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the candidate-policy count assumption](hyp:hM), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the value gap](hyp:gap), [the policy](hyp:p), [the gap0 assumption](hyp:hgap0),
[the models](hyp:models), [the class assumption](hyp:hClass),
[the value gap assumption](hyp:hgap), and [the test assumption](hyp:htest), this establishes
[the testing average error bound minimax regret result](goal). -/
-- @node: testing_average_error_le_minimaxRegret
lemma testing_average_error_le_minimaxRegret {T M : Nat} (hM : 2 ≤ M)
    (t0 zeta C gap p : ℝ) (hgap0 : 0 ≤ gap)
    (models : Fin M → ModelIndex T M)
    (hClass : ∀ v, PolicyListClass t0 zeta C (models v))
    (hgap : ∀ v w, w ≠ v →
      gap ≤ policyValue (models v) v - policyValue (models v) w)
    (htest : ∀ sel : ObservableSelector T M,
      p ≤ (M : ℝ)⁻¹ * ∑ v, (obsLaw (models v).Mx.toRawB).real
        {w | sel.1 (models v).nX (models v).Mx.b (models v).Mx.E w ≠ v}) :
    gap * p ≤ minimaxRegret T M t0 zeta C := by
  apply testing_average_le_minimaxRegret hM t0 zeta C _ models hClass
  intro sel
  calc
    gap * p ≤ gap * ((M : ℝ)⁻¹ * ∑ v,
        (obsLaw (models v).Mx.toRawB).real
          {w | sel.1 (models v).nX (models v).Mx.b (models v).Mx.E w ≠ v}) :=
      mul_le_mul_of_nonneg_left (htest sel) hgap0
    _ = (M : ℝ)⁻¹ * ∑ v, gap * (obsLaw (models v).Mx.toRawB).real
        {w | sel.1 (models v).nX (models v).Mx.b (models v).Mx.E w ≠ v} := by
      rw [← Finset.mul_sum]; ring
    _ ≤ (M : ℝ)⁻¹ * ∑ v, expectedRegret sel (models v) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun v _ ↦
        testing_expectedRegret_gap t0 zeta C sel (models v) (hClass v) v gap (hgap v)

/-- The infimum defining the optimal testing error is nonnegative. For
[the sample space](hyp:Ω), [the candidate-policy count](hyp:M),
[the candidate-policy count assumption](hyp:hM), and [the probability law](hyp:P), this
establishes [the testing fano average error nonnegativity result](goal). -/
-- @node: testing_fanoAverageError_nonneg
lemma testing_fanoAverageError_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (M : Nat) (hM : 0 < M) (P : Fin M → Measure Ω) :
    0 ≤ fanoAverageError M P := by
  let : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  let : Nonempty {ψ : Ω → Fin M // Measurable ψ} :=
    ⟨⟨fun _ ↦ ⟨0, hM⟩, measurable_const⟩⟩
  apply le_ciInf
  intro ψ
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun _ _ ↦ measureReal_nonneg)

/-- A probability experiment has optimal testing error at most one. For
[the sample space](hyp:Ω), [the candidate-policy count](hyp:M),
[the candidate-policy count assumption](hyp:hM), [the probability law](hyp:P), and
[the probability law assumption](hyp:hP), this establishes
[the testing fano average error bound one result](goal). -/
-- @node: testing_fanoAverageError_le_one
lemma testing_fanoAverageError_le_one {Ω : Type*} [MeasurableSpace Ω]
    (M : Nat) (hM : 0 < M) (P : Fin M → Measure Ω)
    (hP : ∀ v, IsProbabilityMeasure (P v)) :
    fanoAverageError M P ≤ 1 := by
  have hpos : (0 : ℝ) < M := by exact_mod_cast hM
  calc
    fanoAverageError M P ≤ (M : ℝ)⁻¹ * ∑ v, (P v).real
        {w | (⟨0, hM⟩ : Fin M) ≠ v} :=
      testing_fanoAverageError_le M P (fun _ ↦ ⟨0, hM⟩) measurable_const
    _ ≤ (M : ℝ)⁻¹ * ∑ _ : Fin M, (1 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro v _
      let := hP v
      exact measureReal_le_one
    _ = 1 := by simp [ne_of_gt hpos]

/-- A coarse logarithmic certificate controls binary entropy at one eighth. This establishes
[the testing bin entropy eighth bound result](goal). -/
-- @node: testing_binEntropy_eighth_bound
lemma testing_binEntropy_eighth_bound :
    Real.binEntropy (1 / 8) ≤ (5 / 8) * Real.log 2 := by
  have htwo := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
  have hseven := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 / 7 by norm_num)
  have hloghalf : Real.log (1 / 2) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  have hlogeighth : Real.log (1 / 8) = -3 * Real.log 2 := by
    rw [one_div, Real.log_inv, show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    ring
  have hlogseven : Real.log (7 / 8) = -Real.log (8 / 7) := by
    rw [show (7 / 8 : ℝ) = (8 / 7)⁻¹ by norm_num, Real.log_inv]
  rw [hloghalf] at htwo
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog_def]
  rw [show (1 - 1 / 8 : ℝ) = 7 / 8 by norm_num,
    hlogeighth, hlogseven]
  nlinarith

/-- The entropy side of Fano cannot support error at most one eighth at the paper's
one-thirty-second average KL budget, for every list size at least two. For
[the candidate-policy count](hyp:M), [the candidate-policy count assumption](hyp:hM),
[the policy](hyp:p), [the p0 assumption](hyp:hp0), and [the event family assumption](hyp:hF),
this establishes [the testing fano entropy floor result](goal). -/
-- @node: testing_fano_entropy_floor
lemma testing_fano_entropy_floor (M : Nat) (hM : 2 ≤ M) (p : ℝ)
    (hp0 : 0 ≤ p)
    (hF : Real.log (M : ℝ) - Real.log (M : ℝ) / 32 ≤
      Real.binEntropy p + p * Real.log ((M - 1 : Nat) : ℝ)) :
    1 / 8 < p := by
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hlogpos : 0 < Real.log (M : ℝ) := Real.log_pos (by linarith)
  have hlogtwo : Real.log 2 ≤ Real.log (M : ℝ) :=
    Real.log_le_log (by norm_num) hMr
  have hsub : (1 : ℝ) ≤ ((M - 1 : Nat) : ℝ) := by
    exact_mod_cast (show 1 ≤ M - 1 by omega)
  have hsublog0 : 0 ≤ Real.log ((M - 1 : Nat) : ℝ) := Real.log_nonneg hsub
  have hsublog : Real.log ((M - 1 : Nat) : ℝ) ≤ Real.log (M : ℝ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast Nat.sub_le M 1)
  by_contra hp
  have hp : p ≤ 1 / 8 := le_of_not_gt hp
  have hent : Real.binEntropy p ≤ Real.binEntropy (1 / 8) :=
    Real.binEntropy_strictMonoOn.monotoneOn ⟨hp0, by linarith⟩
      ⟨by norm_num, by norm_num⟩ hp
  have hmul := mul_le_mul_of_nonneg_right hp hsublog0
  have hb := testing_binEntropy_eighth_bound
  nlinarith

/-- The proved Fano inequality and a small mixture KL budget force the uniform one-eighth testing
error floor used by both lower experiments. For [the sample space](hyp:Ω),
[the candidate-policy count](hyp:M),
[the candidate-policy count assumption](hyp:hM), [the probability law](hyp:P),
[the probability law assumption](hyp:hP), and [the KL assumption](hyp:hKL), this establishes
[the testing fano small mixture KL result](goal). -/
-- @node: testing_fano_small_mixture_kl
lemma testing_fano_small_mixture_kl {Ω : Type} [MeasurableSpace Ω]
    (M : Nat) (hM : 2 ≤ M)
    (P : Fin M → Measure Ω) (hP : ∀ v, IsProbabilityMeasure (P v))
    (hKL : (M : ℝ)⁻¹ * ∑ v,
      (InformationTheory.klDiv (P v) (fanoMixture M P)).toReal ≤
        Real.log (M : ℝ) / 32) :
    1 / 8 < fanoAverageError M P := by
  apply testing_fano_entropy_floor M hM _
    (testing_fanoAverageError_nonneg M (by omega) P)
  exact (sub_le_sub_left hKL _).trans (FanoAverageTesting Ω M hM P hP)

/-- Every measurable test inherits the optimal-error floor. For [the sample space](hyp:Ω),
[the candidate-policy count](hyp:M), [the candidate-policy count assumption](hyp:hM),
[the probability law](hyp:P), [the probability law assumption](hyp:hP),
[the KL assumption](hyp:hKL), [the ψ](hyp:ψ), and [the ψ assumption](hyp:hψ), this establishes
[the testing test error of small mixture KL result](goal). -/
-- @node: testing_test_error_of_small_mixture_kl
lemma testing_test_error_of_small_mixture_kl {Ω : Type} [MeasurableSpace Ω]
    (M : Nat) (hM : 2 ≤ M)
    (P : Fin M → Measure Ω) (hP : ∀ v, IsProbabilityMeasure (P v))
    (hKL : (M : ℝ)⁻¹ * ∑ v,
      (InformationTheory.klDiv (P v) (fanoMixture M P)).toReal ≤
        Real.log (M : ℝ) / 32)
    (ψ : Ω → Fin M) (hψ : Measurable ψ) :
    1 / 8 < (M : ℝ)⁻¹ * ∑ v, (P v).real {w | ψ w ≠ v} := by
  exact (testing_fano_small_mixture_kl M hM P hP hKL).trans_le
    (testing_fanoAverageError_le M P ψ hψ)

end CausalSmith.Stat.PomdpPolicyclassRegret
