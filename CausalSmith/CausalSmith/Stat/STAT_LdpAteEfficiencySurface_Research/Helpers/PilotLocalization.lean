module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotGrowth
public import Causalean.Stat.Concentration.Matrix.IidSums

/-! # Quantitative localization of the randomized-response pilot -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

variable (select : TrialParameter → StaircaseWeight × ℝ × ℝ)

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- The affine inverse applied to one released-category frequency. For the displayed inputs and conditions, the stated result follows. [The pilot Inverse Frequency](goal) is determined by [the displayed parameters](hyp:ε,x). -/
def pilotInverseFrequency (ε x : ℝ) : ℝ :=
  ((Real.exp ε + 3) * x - 1) / (Real.exp ε - 1)

/-- Under the supplied quantities and conditions, the pilot inverse frequency sub private mass assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hε), [the pilot Inverse Frequency sub private Mass](goal).

Under the stated assumptions, the pilot Inverse Frequency sub private Mass. -/
lemma pilotInverseFrequency_sub_privateMass (θ : TrialParameter) (p ε x : ℝ)
    (hε : 0 < ε) (k : Fin 4) :
    pilotInverseFrequency ε x - piTheta θ p k =
      (Real.exp ε + 3) / (Real.exp ε - 1) *
        (x - ∑ j : Fin 4, piTheta θ p j * rrPilotProbability ε j k) := by
  have he : Real.exp ε - 1 ≠ 0 := by
    have : 1 < Real.exp ε := by
      simpa using (Real.exp_lt_exp.mpr hε : Real.exp 0 < Real.exp ε)
    linarith
  rw [pilotInverseFrequency, rrPilot_marginal_probability]
  field_simp [he, ne_of_gt (by positivity : 0 < Real.exp ε + 3)]
  ring

/-- Under the supplied quantities and conditions, the pilot inverse frequency error abs assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hε), [the pilot Inverse Frequency error abs](goal).

Under the stated assumptions, the pilot Inverse Frequency error abs. -/
lemma pilotInverseFrequency_error_abs (θ : TrialParameter) (p ε x : ℝ)
    (hε : 0 < ε) (k : Fin 4) :
    |pilotInverseFrequency ε x - piTheta θ p k| =
      (Real.exp ε + 3) / (Real.exp ε - 1) *
        |x - ∑ j : Fin 4, piTheta θ p j * rrPilotProbability ε j k| := by
  rw [pilotInverseFrequency_sub_privateMass θ p ε x hε k, abs_mul]
  have hn : 0 ≤ (Real.exp ε + 3) / (Real.exp ε - 1) := by
    have : 1 < Real.exp ε := by
      simpa using (Real.exp_lt_exp.mpr hε : Real.exp 0 < Real.exp ε)
    positivity
  rw [abs_of_nonneg hn]

/-- Clipping does not change a raw inverse which lies in its clipping interval. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hδleft,hδright,hx), [the clip Interior eq of abs sub lt](goal).

Under the stated assumptions, the clip Interior eq of abs sub lt. -/
lemma clipInterior_eq_of_abs_sub_lt {δ x θ r : ℝ}
    (hδleft : δ + r ≤ θ) (hδright : δ + r ≤ 1 - θ)
    (hx : |x - θ| < r) :
    clipInterior δ x = x := by
  apply clipInterior_eq_self
  · linarith [(abs_lt.mp hx).1]
  · linarith [(abs_lt.mp hx).2]

/-- A sufficiently accurate pair of calibrated pilot frequencies puts the clipped pilot estimate in the fixed coordinatewise `r`-neighborhood of the truth. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε,hr,hδ0l,hδ0r,hδ1l,hδ1r,hfreq0,hfreq1), [the pilot Theta localized of frequency](goal).

Under the stated assumptions, the pilot Theta localized of frequency. -/
lemma pilotTheta_localized_of_frequency
    (θ : TrialParameter) (p ε r : ℝ) (m : ℕ → ℕ) {n : ℕ}
    (z : Transcript (pilotOutputFamily n))
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hr : 0 < r)
    (hδ0l : (m n + 2 : ℝ)⁻¹ + r ≤ θ 0)
    (hδ0r : (m n + 2 : ℝ)⁻¹ + r ≤ 1 - θ 0)
    (hδ1l : (m n + 2 : ℝ)⁻¹ + r ≤ θ 1)
    (hδ1r : (m n + 2 : ℝ)⁻¹ + r ≤ 1 - θ 1)
    (hfreq0 : |pilotFrequency m z 1 -
        ∑ j : Fin 4, piTheta θ p j * rrPilotProbability ε j 1| <
      r * controlProb p * (Real.exp ε - 1) / (Real.exp ε + 3))
    (hfreq1 : |pilotFrequency m z 3 -
        ∑ j : Fin 4, piTheta θ p j * rrPilotProbability ε j 3| <
      r * p * (Real.exp ε - 1) / (Real.exp ε + 3)) :
    |pilotTheta p ε m z 0 - θ 0| < r ∧
      |pilotTheta p ε m z 1 - θ 1| < r := by
  have hep : 1 < Real.exp ε := by
    simpa using (Real.exp_lt_exp.mpr hε : Real.exp 0 < Real.exp ε)
  have hcp : 0 < controlProb p := by
    dsimp [controlProb]
    linarith [hp.2]
  have hraw0 :
      |pilotInverseFrequency ε (pilotFrequency m z 1) / controlProb p - θ 0| < r := by
    have hpi : piTheta θ p 1 = controlProb p * θ 0 := rfl
    have htheta : θ 0 = piTheta θ p 1 / controlProb p := by
      rw [hpi]
      field_simp
    rw [htheta, ← sub_div]
    have herr := pilotInverseFrequency_error_abs θ p ε (pilotFrequency m z 1) hε 1
    rw [abs_div, abs_of_pos hcp, herr]
    apply (div_lt_iff₀ hcp).2
    calc
      (Real.exp ε + 3) / (Real.exp ε - 1) *
          |pilotFrequency m z 1 -
            ∑ j : Fin 4, piTheta θ p j * rrPilotProbability ε j 1| <
          (Real.exp ε + 3) / (Real.exp ε - 1) *
            (r * controlProb p * (Real.exp ε - 1) / (Real.exp ε + 3)) := by
        gcongr <;> positivity
      _ = r * controlProb p := by
        field_simp [ne_of_gt (sub_pos.mpr hep), ne_of_gt (by positivity : 0 < Real.exp ε + 3)]
  have hraw1 :
      |pilotInverseFrequency ε (pilotFrequency m z 3) / p - θ 1| < r := by
    have hp0 : 0 < p := hp.1
    have hpi : piTheta θ p 3 = p * θ 1 := rfl
    have htheta : θ 1 = piTheta θ p 3 / p := by
      rw [hpi]
      field_simp
    rw [htheta, ← sub_div]
    have herr := pilotInverseFrequency_error_abs θ p ε (pilotFrequency m z 3) hε 3
    rw [abs_div, abs_of_pos hp0, herr]
    apply (div_lt_iff₀ hp0).2
    calc
      (Real.exp ε + 3) / (Real.exp ε - 1) *
          |pilotFrequency m z 3 -
            ∑ j : Fin 4, piTheta θ p j * rrPilotProbability ε j 3| <
          (Real.exp ε + 3) / (Real.exp ε - 1) *
            (r * p * (Real.exp ε - 1) / (Real.exp ε + 3)) := by
        gcongr <;> positivity
      _ = r * p := by
        field_simp [ne_of_gt (sub_pos.mpr hep), ne_of_gt (by positivity : 0 < Real.exp ε + 3)]
  have hclip0 := clipInterior_eq_of_abs_sub_lt hδ0l hδ0r hraw0
  have hclip1 := clipInterior_eq_of_abs_sub_lt hδ1l hδ1r hraw1
  constructor
  · change |clipInterior (m n + 2 : ℝ)⁻¹
        (pilotInverseFrequency ε (pilotFrequency m z 1) / controlProb p) - θ 0| < r
    rw [hclip0]
    exact hraw0
  · change |clipInterior (m n + 2 : ℝ)⁻¹
        (pilotInverseFrequency ε (pilotFrequency m z 3) / p) - θ 1| < r
    rw [hclip1]
    exact hraw1

/-- Uniform Chebyshev concentration of one released pilot-cell frequency. The bound is parameter free apart from the exact centering probability. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hmn,hmpos,ha), [the pilot Frequency deviation le](goal).

Under the stated assumptions, the pilot Frequency deviation le. -/
lemma pilotFrequency_deviation_le
    (θ : TrialParameter) (p ε a : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    {n : ℕ} (hmn : m n ≤ n) (hmpos : 0 < m n) (ha : 0 < a) (k : Fin 4) :
    (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n)
        {z | a ≤ |pilotFrequency m z k -
          ∑ j : Fin 4, piTheta θ p j * rrPilotProbability ε j k|} ≤
      ENNReal.ofReal (1 / ((m n : ℝ) * a ^ 2)) := by
  let P := rrPilotMarginal θ p ε
  letI : IsProbabilityMeasure P := rrPilotMarginal_isProbability θ p ε hp hθ
  let g := pilotCellIndicator k
  have hg : MemLp g 2 P := by
    apply MemLp.of_bound (measurable_pilotCellIndicator k).aestronglyMeasurable 1
    filter_upwards [] with x
    dsimp [g, pilotCellIndicator]
    split_ifs <;> norm_num
  have hcheb := Causalean.Stat.Concentration.iid_sum_chebyshev
    (N := m n) P g hg (mul_pos (Nat.cast_pos.mpr hmpos) ha)
  have hvar : Var[g; P] ≤ 1 := by
    have hg2 : Integrable (fun x => (g x) ^ 2) P := by
      apply Integrable.of_bound
        ((measurable_pilotCellIndicator k).pow_const 2).aestronglyMeasurable 1
      filter_upwards [] with x
      dsimp [g, pilotCellIndicator]
      split_ifs <;> norm_num
    calc
      Var[g; P] ≤ ∫ x, (g x) ^ 2 ∂P := variance_le_expectation_sq hg.aestronglyMeasurable
      _ ≤ 1 := by
        have hpoint : ∀ x, (g x) ^ 2 ≤ (1 : ℝ) := by
          intro x
          dsimp [g, pilotCellIndicator]
          split_ifs <;> norm_num
        calc
          (∫ x, (g x) ^ 2 ∂P) ≤ ∫ _x, (1 : ℝ) ∂P := by
            apply integral_mono_ae hg2 (integrable_const 1)
            exact Filter.Eventually.of_forall hpoint
          _ = 1 := by simp
  have hlaw := pilotFrequency_map_eq_pi select θ p ε m hselect hp hθ hε hmn k
  have hfreq : Measurable (fun z : Transcript (pilotOutputFamily n) =>
      pilotFrequency m z k) := measurable_pilotFrequency m k
  have hsum : Measurable (fun u : Fin (m n) → Fin 4 =>
      ∑ i : Fin (m n), g (u i)) := by fun_prop
  let q := ∑ j : Fin 4, piTheta θ p j * rrPilotProbability ε j k
  have hmean : ∫ x, g x ∂P = q := integral_pilotCellIndicator θ p ε hp hθ k
  let B : Set ℝ := {x | a ≤ |x - q|}
  have hB : MeasurableSet B := by
    exact measurableSet_le measurable_const
      ((measurable_id.sub measurable_const).abs)
  change (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n)
      ((fun z => pilotFrequency m z k) ⁻¹' B) ≤ _
  rw [← Measure.map_apply hfreq hB, hlaw, Measure.map_apply (by fun_prop) hB]
  have hevent : {u : Fin (m n) → Fin 4 | a ≤ |pilotPrefixFrequency u k - q|} =
      {u | (m n : ℝ) * a ≤
        |(∑ i : Fin (m n), g (u i)) - (m n : ℝ) * ∫ x, g x ∂P|} := by
    ext u
    simp only [Set.mem_setOf_eq, pilotPrefixFrequency]
    have hmne : (m n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hmpos)
    change a ≤ |(m n : ℝ)⁻¹ * ∑ j : Fin (m n), g (u j) - q| ↔
      (m n : ℝ) * a ≤
        |(∑ j : Fin (m n), g (u j)) - (m n : ℝ) * ∫ x, g x ∂P|
    rw [hmean, inv_eq_one_div]
    have hid : (m n : ℝ) *
        ((1 / (m n : ℝ) * ∑ j : Fin (m n), g (u j)) - q) =
        (∑ j : Fin (m n), g (u j)) - (m n : ℝ) * q := by
      field_simp [hmne]
    have habs : |(∑ j : Fin (m n), g (u j)) - (m n : ℝ) * q| =
        (m n : ℝ) *
          |(1 / (m n : ℝ) * ∑ j : Fin (m n), g (u j)) - q| := by
      rw [← hid, abs_mul, abs_of_pos (Nat.cast_pos.mpr hmpos)]
    constructor <;> intro h
    · rw [habs]
      exact (mul_le_mul_iff_of_pos_left (Nat.cast_pos.mpr hmpos)).2 h
    · rw [habs] at h
      exact (mul_le_mul_iff_of_pos_left (Nat.cast_pos.mpr hmpos)).1 h
  change (Measure.pi fun _ : Fin (m n) => rrPilotMarginal θ p ε)
      {u | a ≤ |pilotPrefixFrequency u k - q|} ≤ _
  rw [hevent]
  calc
    _ ≤ ENNReal.ofReal
        ((m n : ℝ) * Var[g; P] / ((m n : ℝ) * a) ^ 2) := hcheb
    _ ≤ ENNReal.ofReal (1 / ((m n : ℝ) * a ^ 2)) := by
      apply ENNReal.ofReal_le_ofReal
      have hm0 : 0 < (m n : ℝ) := Nat.cast_pos.mpr hmpos
      calc
        (m n : ℝ) * Var[g; P] / ((m n : ℝ) * a) ^ 2 ≤
            (m n : ℝ) * 1 / ((m n : ℝ) * a) ^ 2 := by
          gcongr
        _ = 1 / ((m n : ℝ) * a ^ 2) := by field_simp

/-- The two-coordinate clipped pilot leaves an `r`-neighborhood of its true parameter with probability at most the sum of two parameter-uniform Chebyshev bounds. This form applies row by row to local parameter sequences. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hr,hmn,hmpos,hδ0l,hδ0r,hδ1l,hδ1r), [the pilot Theta deviation le](goal).

Under the stated assumptions, the pilot Theta deviation le. -/
lemma pilotTheta_deviation_le
    (θ : TrialParameter) (p ε r : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hr : 0 < r) {n : ℕ} (hmn : m n ≤ n) (hmpos : 0 < m n)
    (hδ0l : (m n + 2 : ℝ)⁻¹ + r ≤ θ 0)
    (hδ0r : (m n + 2 : ℝ)⁻¹ + r ≤ 1 - θ 0)
    (hδ1l : (m n + 2 : ℝ)⁻¹ + r ≤ θ 1)
    (hδ1r : (m n + 2 : ℝ)⁻¹ + r ≤ 1 - θ 1) :
    let a0 := r * controlProb p * (Real.exp ε - 1) / (Real.exp ε + 3)
    let a1 := r * p * (Real.exp ε - 1) / (Real.exp ε + 3)
    (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n)
        {z | r ≤ |pilotTheta p ε m z 0 - θ 0| ∨
          r ≤ |pilotTheta p ε m z 1 - θ 1|} ≤
      ENNReal.ofReal (1 / ((m n : ℝ) * a0 ^ 2)) +
        ENNReal.ofReal (1 / ((m n : ℝ) * a1 ^ 2)) := by
  dsimp only
  let q0 := ∑ j : Fin 4, piTheta θ p j * rrPilotProbability ε j 1
  let q1 := ∑ j : Fin 4, piTheta θ p j * rrPilotProbability ε j 3
  let a0 := r * controlProb p * (Real.exp ε - 1) / (Real.exp ε + 3)
  let a1 := r * p * (Real.exp ε - 1) / (Real.exp ε + 3)
  have ha0 : 0 < a0 := by
    dsimp [a0, controlProb]
    have hep : 1 < Real.exp ε := by
      simpa using (Real.exp_lt_exp.mpr hε : Real.exp 0 < Real.exp ε)
    exact div_pos (mul_pos (mul_pos hr (by linarith [hp.2])) (by linarith)) (by positivity)
  have ha1 : 0 < a1 := by
    dsimp [a1]
    have hep : 1 < Real.exp ε := by
      simpa using (Real.exp_lt_exp.mpr hε : Real.exp 0 < Real.exp ε)
    exact div_pos (mul_pos (mul_pos hr hp.1) (by linarith)) (by positivity)
  let A0 : Set (Transcript (pilotOutputFamily n)) :=
    {z | a0 ≤ |pilotFrequency m z 1 - q0|}
  let A1 : Set (Transcript (pilotOutputFamily n)) :=
    {z | a1 ≤ |pilotFrequency m z 3 - q1|}
  have hsub : {z | r ≤ |pilotTheta p ε m z 0 - θ 0| ∨
      r ≤ |pilotTheta p ε m z 1 - θ 1|} ⊆ A0 ∪ A1 := by
    intro z hz
    by_contra hzunion
    have hz0 : |pilotFrequency m z 1 - q0| < a0 := by
      exact lt_of_not_ge (fun h => hzunion (Set.mem_union_left A1 h))
    have hz1 : |pilotFrequency m z 3 - q1| < a1 := by
      exact lt_of_not_ge (fun h => hzunion (Set.mem_union_right A0 h))
    have hloc := pilotTheta_localized_of_frequency θ p ε r m z hp hθ hε hr
      hδ0l hδ0r hδ1l hδ1r (by simpa [a0, q0] using hz0)
      (by simpa [a1, q1] using hz1)
    exact hz.elim (fun h => (not_le_of_gt hloc.1) h)
      (fun h => (not_le_of_gt hloc.2) h)
  let μ := transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n
  calc
    μ {z | r ≤ |pilotTheta p ε m z 0 - θ 0| ∨
        r ≤ |pilotTheta p ε m z 1 - θ 1|} ≤ μ (A0 ∪ A1) := measure_mono hsub
    _ ≤ μ A0 + μ A1 := measure_union_le A0 A1
    _ ≤ ENNReal.ofReal (1 / ((m n : ℝ) * a0 ^ 2)) +
        ENNReal.ofReal (1 / ((m n : ℝ) * a1 ^ 2)) := by
      apply add_le_add
      · simpa [μ, A0, a0, q0] using
          pilotFrequency_deviation_le select θ p ε a0 m hselect hp hθ hε hmn hmpos ha0 1
      · simpa [μ, A1, a1, q1] using
          pilotFrequency_deviation_le select θ p ε a1 m hselect hp hθ hε hmn hmpos ha1 3

end CausalSmith.Stat.LdpAteEfficiencySurface
