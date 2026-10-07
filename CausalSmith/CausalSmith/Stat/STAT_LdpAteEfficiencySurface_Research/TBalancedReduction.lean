module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.BalancedBinary
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # Balanced randomized-response reduction

When assignment is balanced and the arm means sum to one, randomized response
to the signed treatment–outcome bit attains the information oracle. -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory
open scoped ENNReal

open BalancedBinary

/-- the [signed bit](goal) is the mathematical object specified below. -/
def signedBit : Fin 4 → Fin 2
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 0
  | _ => 1

/-- the balanced rr is the mathematical object specified below. [The balanced RR](goal) is determined by [the displayed parameters](hyp:ε). -/
def balancedRR (ε : ℝ) : Kernel (Fin 4) (Fin 2) :=
  Kernel.ofFunOfCountable fun j =>
    Measure.count.withDensity (fun z : Fin 2 =>
      ENNReal.ofReal
        (if z = signedBit j then Real.exp ε / (Real.exp ε + 1)
         else 1 / (Real.exp ε + 1)))

/-- Under [the supplied quantities and conditions](hyp:j,z), [the balanced rr atom assertion](goal) holds. -/
lemma balancedRR_atom (ε : ℝ) (j : Fin 4) (z : Fin 2) :
    ((balancedRR ε j) {z}).toReal =
      if z = signedBit j then Real.exp ε / (Real.exp ε + 1)
      else 1 / (Real.exp ε + 1) := by
  have he : 0 < Real.exp ε := Real.exp_pos ε
  have hd : 0 < Real.exp ε + 1 := by positivity
  change (Measure.count.withDensity (fun u : Fin 2 => ENNReal.ofReal
    (if u = signedBit j then Real.exp ε / (Real.exp ε + 1)
      else 1 / (Real.exp ε + 1))) {z}).toReal = _
  rw [withDensity_apply _ (measurableSet_singleton z), lintegral_singleton]
  have hc : Measure.count {z} = 1 := by simp
  rw [hc, mul_one]
  split_ifs <;> rw [ENNReal.toReal_ofReal] <;> positivity

/-- Under [the supplied quantities and conditions](hyp:b,z), [the grouped balanced rr atom assertion](goal) holds. -/
lemma grouped_balancedRR_atom (ε : ℝ) (b : Bool) (z : Fin 2) :
    ((groupedChannel (balancedRR ε) b) {z}).toReal =
      if b = (z = 1) then Real.exp ε / (Real.exp ε + 1)
      else 1 / (Real.exp ε + 1) := by
  have hfinite (j : Fin 4) : balancedRR ε j {z} ≠ ∞ := by
    intro hj
    have h := balancedRR_atom ε j z
    rw [hj] at h
    simp only [ENNReal.toReal_top] at h
    split_ifs at h
    · have hp : 0 < Real.exp ε / (Real.exp ε + 1) := by positivity
      linarith
    · have hq : 0 < 1 / (Real.exp ε + 1) := by positivity
      linarith
  have hhalfReal : half.toReal = (1 / 2 : ℝ) := by rfl
  cases b
  · change (half * (balancedRR ε 1 {z} + balancedRR ε 2 {z})).toReal = _
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_add (hfinite 1) (hfinite 2)]
    rw [balancedRR_atom, balancedRR_atom]
    fin_cases z <;> rw [hhalfReal] <;> simp +decide [signedBit] <;>
      field_simp <;> ring
  · change (half * (balancedRR ε 0 {z} + balancedRR ε 3 {z})).toReal = _
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_add (hfinite 0) (hfinite 3)]
    rw [balancedRR_atom, balancedRR_atom]
    fin_cases z <;> rw [hhalfReal] <;> simp +decide [signedBit] <;>
      field_simp <;> ring

/-- Under [the supplied quantities and conditions](hyp:b,z), [the randomized response atom assertion](goal) holds. -/
lemma randomizedResponse_atom (ε : ℝ) (b z : Bool) :
    ((Causalean.Stat.Privacy.Binary.randomizedResponse ε b) {z}).toReal =
      if b = z then Real.exp ε / (Real.exp ε + 1)
      else 1 / (Real.exp ε + 1) := by
  let e := Real.exp ε
  let p := e / (e + 1)
  let q := 1 / (e + 1)
  have he : 0 < e := by dsimp [e]; positivity
  have he1 : 0 < e + 1 := by linarith
  have hp : 0 < p := div_pos he he1
  have hq : 0 < q := div_pos (by norm_num) he1
  have hcq : 1 - q = p := by
    dsimp [p, q]
    field_simp
    ring
  have hcp : 1 - p = q := by
    dsimp [p, q]
    field_simp
    ring
  have hqi : (Real.exp ε + 1)⁻¹ = q := by
    dsimp [q, e]
    rw [one_div]
  change ((Causalean.Mathlib.Probability.bernoulliBool
    (Causalean.Stat.Privacy.Binary.responseProbability ε b)) {z}).toReal = _
  cases b <;> cases z <;>
    simp [Causalean.Stat.Privacy.Binary.responseProbability,
      Causalean.Mathlib.Probability.bernoulliBool,
      Measure.add_apply, Measure.smul_apply]
  all_goals try rw [hqi]
  all_goals try positivity
  all_goals first
    | (change (ENNReal.ofReal (1 - q)).toReal = p
       rw [hcq, ENNReal.toReal_ofReal hp.le])
    | (change (ENNReal.ofReal q).toReal = q
       rw [ENNReal.toReal_ofReal hq.le])
    | (change (ENNReal.ofReal (1 - p)).toReal = q
       rw [hcp, ENNReal.toReal_ofReal hq.le])
    | (change (ENNReal.ofReal p).toReal = p
       rw [ENNReal.toReal_ofReal hp.le])

-- @node: piTheta_balanced_by_val
/-- Under [the supplied quantities and conditions](hyp:j), [the pi theta balanced by val assertion](goal) holds. -/
lemma piTheta_balanced_by_val (θ : TrialParameter) (j : Fin 4) :
    piTheta θ (1 / 2) j =
      if j.val = 0 then controlProb (1 / 2) * (1 - θ 0)
      else if j.val = 1 then controlProb (1 / 2) * θ 0
      else if j.val = 2 then (1 / 2) * (1 - θ 1)
      else (1 / 2) * θ 1 := by
  rcases j with ⟨j, hj⟩
  interval_cases j <;> rfl

-- @node: signedBit_probability_one
/-- [the signed bit probability one assertion](goal) holds. -/
lemma signedBit_probability_one (θ : TrialParameter) :
    (∑ j : Fin 4, if signedBit j = 1 then piTheta θ (1 / 2) j else 0) =
      (1 + contrast θ) / 2 := by
  simp +decide [signedBit, contrast, Fin.sum_univ_succ]
  rw [← one_div]
  rw [piTheta_balanced_by_val, piTheta_balanced_by_val]
  norm_num [controlProb]
  ring

-- @node: signedBit_probability_zero
/-- [the signed bit probability zero assertion](goal) holds. -/
lemma signedBit_probability_zero (θ : TrialParameter) :
    (∑ j : Fin 4, if signedBit j = 0 then piTheta θ (1 / 2) j else 0) =
      (1 - contrast θ) / 2 := by
  simp +decide [signedBit, contrast, Fin.sum_univ_succ]
  rw [← one_div]
  rw [piTheta_balanced_by_val, piTheta_balanced_by_val]
  norm_num [controlProb]
  ring

-- @node: balancedRR_output_probability_one
/-- [the balanced rr output probability one assertion](goal) holds. -/
lemma balancedRR_output_probability_one (θ : TrialParameter) (ε : ℝ) :
    (∑ j : Fin 4, piTheta θ (1 / 2) j *
      (if (1 : Fin 2) = signedBit j then
        Real.exp ε / (Real.exp ε + 1)
       else 1 / (Real.exp ε + 1))) =
      (1 + (Real.exp ε - 1) / (Real.exp ε + 1) * contrast θ) / 2 := by
  have hd : Real.exp ε + 1 ≠ 0 := by positivity
  simp +decide [signedBit, contrast, Fin.sum_univ_succ]
  rw [← one_div]
  rw [piTheta_balanced_by_val, piTheta_balanced_by_val,
    piTheta_balanced_by_val, piTheta_balanced_by_val]
  norm_num [controlProb]
  field_simp
  ring

-- @node: balancedRR_output_probability_zero
/-- [the balanced rr output probability zero assertion](goal) holds. -/
lemma balancedRR_output_probability_zero (θ : TrialParameter) (ε : ℝ) :
    (∑ j : Fin 4, piTheta θ (1 / 2) j *
      (if (0 : Fin 2) = signedBit j then
        Real.exp ε / (Real.exp ε + 1)
       else 1 / (Real.exp ε + 1))) =
      (1 - (Real.exp ε - 1) / (Real.exp ε + 1) * contrast θ) / 2 := by
  have hd : Real.exp ε + 1 ≠ 0 := by positivity
  simp +decide [signedBit, contrast, Fin.sum_univ_succ]
  rw [← one_div]
  rw [piTheta_balanced_by_val, piTheta_balanced_by_val,
    piTheta_balanced_by_val, piTheta_balanced_by_val]
  norm_num [controlProb]
  field_simp
  ring

/-- Under the supplied quantities and conditions, the balanced rr stationary assertion holds. Under [the stated assumptions](hyp:hε), [the balanced RR stationary](goal).

Under the stated assumptions, the balanced RR stationary. -/
lemma balancedRR_stationary (ε : ℝ) (hε : 0 < ε) :
    StationaryLDP ε (balancedRR ε) := by
  constructor
  · constructor
    intro j
    constructor
    have hsum : (∑ z : Fin 2,
        (if z = signedBit j then Real.exp ε / (Real.exp ε + 1)
         else 1 / (Real.exp ε + 1))) = 1 := by
      fin_cases j <;> simp +decide [signedBit, Fin.sum_univ_succ] <;>
        field_simp <;> ring
    rw [← ENNReal.ofReal_one, ← hsum]
    change (Measure.count.withDensity
      (fun z : Fin 2 => ENNReal.ofReal
        (if z = signedBit j then Real.exp ε / (Real.exp ε + 1)
         else 1 / (Real.exp ε + 1)))) Set.univ = _
    simp only [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      lintegral_count]
    rw [tsum_fintype, ENNReal.ofReal_sum_of_nonneg]
    intro z hz
    split_ifs <;> positivity
  · intro A hA j j'
    let r := ENNReal.ofReal (Real.exp ε)
    have hr : r ≠ ∞ := ENNReal.ofReal_ne_top
    have hm : Measure.count.withDensity
        (fun z : Fin 2 => ENNReal.ofReal
          (if z = signedBit j then Real.exp ε / (Real.exp ε + 1)
           else 1 / (Real.exp ε + 1))) ≤
        r • Measure.count.withDensity
          (fun z : Fin 2 => ENNReal.ofReal
            (if z = signedBit j' then Real.exp ε / (Real.exp ε + 1)
             else 1 / (Real.exp ε + 1))) := by
      rw [← withDensity_smul' r _ hr]
      apply withDensity_mono
      filter_upwards [] with z
      dsimp [r]
      rw [← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos ε))]
      apply ENNReal.ofReal_le_ofReal
      have he : 1 ≤ Real.exp ε := (Real.one_le_exp_iff).2 (le_of_lt hε)
      have hd : 0 < Real.exp ε + 1 := by positivity
      split_ifs <;> rw [← mul_div_assoc] <;>
        apply (div_le_div_iff_of_pos_right hd).2 <;>
        nlinarith [sq_nonneg (Real.exp ε - 1)]
    exact hm A

/-- Under the supplied quantities and conditions, the grouped balanced rr information eq randomized response assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hθ,hbalance,hε), [the grouped balanced RR information eq randomized Response](goal).

Under the stated assumptions, the grouped balanced RR information eq randomized Response. -/
lemma grouped_balancedRR_information_eq_randomizedResponse
    (θ : TrialParameter) (hθ : InteriorMeans θ)
    (hbalance : θ 0 + θ 1 = 1) (ε : ℝ) (hε : 0 < ε) :
    Causalean.Stat.Privacy.Binary.information
        (groupedChannel (balancedRR ε)) (contrast θ) =
      Causalean.Stat.Privacy.Binary.information
        (Causalean.Stat.Privacy.Binary.randomizedResponse ε) (contrast θ) := by
  letI : IsMarkovKernel (balancedRR ε) := (balancedRR_stationary ε hε).1
  letI : IsMarkovKernel (groupedChannel (balancedRR ε)) :=
    groupedChannel_markov _
  letI : IsMarkovKernel
      (Causalean.Stat.Privacy.Binary.randomizedResponse ε) :=
    Causalean.Stat.Privacy.Binary.randomizedResponse_markov ε
  have hτ := abs_contrast_lt_one θ hθ hbalance
  rw [Causalean.Stat.Privacy.Binary.information_eq_discrete _ _ hτ,
    Causalean.Stat.Privacy.Binary.information_eq_discrete _ _ hτ]
  unfold Causalean.Stat.Privacy.Binary.discreteInformation
  rw [tsum_fintype, tsum_fintype]
  simp +decide [grouped_balancedRR_atom, randomizedResponse_atom,
    Fin.sum_univ_succ]
  ring

/-- the grouped balanced rr information eq assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hθ,hbalance,hε), [the grouped balanced RR information eq](goal).

Under the stated assumptions, the grouped balanced RR information eq. -/
lemma grouped_balancedRR_information_eq (θ : TrialParameter)
    (hθ : InteriorMeans θ) (hbalance : θ 0 + θ 1 = 1)
    (ε : ℝ) (hε : 0 < ε) :
    Causalean.Stat.Privacy.Binary.information
        (groupedChannel (balancedRR ε)) (contrast θ) =
      Causalean.Stat.Privacy.Binary.contraction ε ^ 2 /
        (1 - Causalean.Stat.Privacy.Binary.contraction ε ^ 2 *
          contrast θ ^ 2) := by
  rw [grouped_balancedRR_information_eq_randomizedResponse
    θ hθ hbalance ε hε]
  exact Causalean.Stat.Privacy.Binary.randomizedResponse_information_eq
    ε (contrast θ) hε (abs_contrast_lt_one θ hθ hbalance)

/-- Under [the supplied quantities and conditions](hyp:t,z), [the balanced rr directional derivative assertion](goal) holds. -/
lemma balancedRR_directionalDerivative (ε t : ℝ) (z : Fin 2) :
    (∑ k, direction t k *
      channelDerivativeDensity (1 / 2) (balancedRR ε) k z) =
    (∑ k, direction (-1 / 2) k *
      channelDerivativeDensity (1 / 2) (balancedRR ε) k z) := by
  have h03 : balancedRR ε 0 = balancedRR ε 3 := by rfl
  have h12 : balancedRR ε 1 = balancedRR ε 2 := by rfl
  have hd03 : channelDensity (balancedRR ε) 0 z =
      channelDensity (balancedRR ε) 3 z := by
    unfold channelDensity
    rw [h03]
  have hd12 : channelDensity (balancedRR ε) 1 z =
      channelDensity (balancedRR ε) 2 z := by
    unfold channelDensity
    rw [h12]
  simp +decide [channelDerivativeDensity, inputDerivative, direction,
    controlProb, Fin.sum_univ_succ]
  rw [hd03, hd12]
  ring

/-- Under the supplied quantities and conditions, the balanced rr quadratic eq assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hθ,hε), [the balanced RR quadratic eq](goal).

Under the stated assumptions, the balanced RR quadratic eq. -/
lemma balancedRR_quadratic_eq (θ : TrialParameter) (hθ : InteriorMeans θ)
    (ε : ℝ) (hε : 0 < ε) (t : ℝ) :
    informationQuadratic (channelFisherInfo θ (1 / 2) (balancedRR ε))
        (direction t) =
      informationQuadratic (channelFisherInfo θ (1 / 2) (balancedRR ε))
        (direction (-1 / 2)) := by
  have hRR := balancedRR_stationary ε hε
  rw [informationQuadratic_eq_channelIntegral (1 / 2) θ
      (by constructor <;> norm_num) hθ ε (balancedRR ε) hRR (direction t),
    informationQuadratic_eq_channelIntegral (1 / 2) θ
      (by constructor <;> norm_num) hθ ε (balancedRR ε) hRR
        (direction (-1 / 2))]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [balancedRR_directionalDerivative ε t z]

/-- Under the supplied quantities and conditions, the sharp information pos assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hθ,hbalance,hε), [the sharp information pos](goal).

Under the stated assumptions, the sharp information pos. -/
lemma sharp_information_pos (θ : TrialParameter) (hθ : InteriorMeans θ)
    (hbalance : θ 0 + θ 1 = 1) (ε : ℝ) (hε : 0 < ε) :
    0 < Causalean.Stat.Privacy.Binary.contraction ε ^ 2 /
      (1 - Causalean.Stat.Privacy.Binary.contraction ε ^ 2 *
        contrast θ ^ 2) := by
  let κ := Causalean.Stat.Privacy.Binary.contraction ε
  have hκ : 0 < κ := by
    dsimp [κ, Causalean.Stat.Privacy.Binary.contraction]
    have he : 1 < Real.exp ε := (Real.one_lt_exp_iff).2 hε
    positivity
  have hκ1 : κ < 1 :=
    (Causalean.Stat.Privacy.Binary.contraction_mem ε hε).2
  have hκSq : κ ^ 2 < 1 := (sq_lt_one_iff₀ hκ.le).2 hκ1
  have hτSq : contrast θ ^ 2 < 1 :=
    (sq_lt_one_iff_abs_lt_one (contrast θ)).2
      (abs_contrast_lt_one θ hθ hbalance)
  have hprod : κ ^ 2 * contrast θ ^ 2 < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left (sq_nonneg κ) hκSq hτSq.le
  exact div_pos (sq_pos_of_pos hκ) (sub_pos.2 hprod)

/-- the balanced rr variance eq sharp assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hθ,hbalance,hε), [the balanced RR variance eq sharp](goal).

Under the stated assumptions, the balanced RR variance eq sharp. -/
lemma balancedRR_variance_eq_sharp (θ : TrialParameter)
    (hθ : InteriorMeans θ) (hbalance : θ 0 + θ 1 = 1)
    (ε : ℝ) (hε : 0 < ε) :
    contrastVariance (channelFisherInfo θ (1 / 2) (balancedRR ε)) =
      ENNReal.ofReal
        (Causalean.Stat.Privacy.Binary.contraction ε ^ 2 /
          (1 - Causalean.Stat.Privacy.Binary.contraction ε ^ 2 *
            contrast θ ^ 2))⁻¹ := by
  have hRR := balancedRR_stationary ε hε
  have hinfo := grouped_balancedRR_information_eq θ hθ hbalance ε hε
  have hquad :
      informationQuadratic
          (channelFisherInfo θ (1 / 2) (balancedRR ε)) (direction (-1 / 2)) =
        Causalean.Stat.Privacy.Binary.contraction ε ^ 2 /
          (1 - Causalean.Stat.Privacy.Binary.contraction ε ^ 2 *
            contrast θ ^ 2) := by
    rw [← hinfo]
    exact grouped_information_eq_channelQuadratic θ hθ hbalance ε
      (balancedRR ε) hRR |>.symm
  rw [contrastVariance_eq_reciprocal_of_minimizer
    (channelFisherInfo θ (1 / 2) (balancedRR ε))
    (channelFisherInfo_posSemidef (1 / 2) θ (by constructor <;> norm_num)
      hθ ε (balancedRR ε) hRR)
    (-1 / 2)
    (fun u => by rw [balancedRR_quadratic_eq θ hθ ε hε u])
    (hquad.symm ▸ sharp_information_pos θ hθ hbalance ε hε),
    hquad]

/-- the vstar balanced eq sharp reciprocal assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hθ,hbalance,hε), [the Vstar balanced eq sharp reciprocal](goal).

Under the stated assumptions, the Vstar balanced eq sharp reciprocal. -/
lemma Vstar_balanced_eq_sharp_reciprocal (θ : TrialParameter)
    (hθ : InteriorMeans θ) (hbalance : θ 0 + θ 1 = 1)
    (ε : ℝ) (hε : 0 < ε) :
    Vstar θ (1 / 2) ε =
      (Causalean.Stat.Privacy.Binary.contraction ε ^ 2 /
        (1 - Causalean.Stat.Privacy.Binary.contraction ε ^ 2 *
          contrast θ ^ 2))⁻¹ := by
  let B := Causalean.Stat.Privacy.Binary.contraction ε ^ 2 /
    (1 - Causalean.Stat.Privacy.Binary.contraction ε ^ 2 * contrast θ ^ 2)
  have hB : 0 < B := sharp_information_pos θ hθ hbalance ε hε
  have hJ : 0 < Jstar θ (1 / 2) ε :=
    Jstar_pos_interior θ (1 / 2) ε (by constructor <;> norm_num) hθ hε
  have hJle : Jstar θ (1 / 2) ε ≤ B := by
    simpa [B] using Jstar_balanced_le_sharp θ hθ hbalance ε hε
  have hlower : B⁻¹ ≤ Vstar θ (1 / 2) ε := by
    rw [Vstar]
    exact (inv_le_inv₀ hB hJ).2 hJle
  have huniv := (finite_oracle θ (1 / 2) ε
    (by constructor <;> norm_num) hθ (fun _ => ε) ⟨hε, fun _ => rfl⟩).1
    (Fin 2) (balancedRR ε) (balancedRR_stationary ε hε)
  rw [balancedRR_variance_eq_sharp θ hθ hbalance ε hε] at huniv
  have hupper : Vstar θ (1 / 2) ε ≤ B⁻¹ := by
    rw [ENNReal.ofReal_le_ofReal_iff (inv_nonneg.mpr hB.le)] at huniv
    simpa [B] using huniv
  exact le_antisymm hupper hlower

/-- Under the supplied quantities and conditions, the contraction inv eq coth assertion holds. Under [the stated assumptions](hyp:hε), [the contraction inv eq coth](goal).

Under the stated assumptions, the contraction inv eq coth. -/
lemma contraction_inv_eq_coth (ε : ℝ) (hε : 0 < ε) :
    (Causalean.Stat.Privacy.Binary.contraction ε)⁻¹ =
      Real.cosh (ε / 2) / Real.sinh (ε / 2) := by
  have hs : Real.sinh (ε / 2) ≠ 0 :=
    ne_of_gt ((Real.sinh_pos_iff).2 (by linarith))
  have he : Real.exp (ε / 2) ≠ 0 := Real.exp_ne_zero _
  have hexp : Real.exp ε = Real.exp (ε / 2) * Real.exp (ε / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Causalean.Stat.Privacy.Binary.contraction, Real.cosh_eq, Real.sinh_eq,
    Real.exp_neg, hexp]
  field_simp

-- @node: thm:balanced-reduction
/-- the balanced reduction assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hθ,hbalance,hε), [the balanced reduction](goal).

Under the stated assumptions, the balanced reduction. -/
theorem balanced_reduction {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y0 Y1 W Y : ℕ → Ω → ℝ)
    (θ : TrialParameter) (ε : ℝ)
    (hθ : InteriorMeans θ)
    (hbalance : θ 0 + θ 1 = 1) (hε : 0 < ε) :
    Vstar θ (1 / 2) ε =
      (Real.cosh (ε / 2) / Real.sinh (ε / 2)) ^ 2 -
        (contrast θ) ^ 2 ∧
    StationaryLDP ε (balancedRR ε) ∧
    contrastVariance (channelFisherInfo θ (1 / 2) (balancedRR ε)) =
      ENNReal.ofReal (Vstar θ (1 / 2) ε) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Vstar_balanced_eq_sharp_reciprocal θ hθ hbalance ε hε]
    let κ := Causalean.Stat.Privacy.Binary.contraction ε
    have hκ : 0 < κ := by
      dsimp [κ, Causalean.Stat.Privacy.Binary.contraction]
      have he : 1 < Real.exp ε := (Real.one_lt_exp_iff).2 hε
      positivity
    have hden : 1 - κ ^ 2 * contrast θ ^ 2 ≠ 0 := by
      have hκ1 : κ < 1 :=
        (Causalean.Stat.Privacy.Binary.contraction_mem ε hε).2
      have hκSq : κ ^ 2 < 1 := (sq_lt_one_iff₀ hκ.le).2 hκ1
      have hτSq : contrast θ ^ 2 < 1 :=
        (sq_lt_one_iff_abs_lt_one (contrast θ)).2
          (abs_contrast_lt_one θ hθ hbalance)
      exact ne_of_gt (sub_pos.2
        (mul_lt_one_of_nonneg_of_lt_one_left
          (sq_nonneg κ) hκSq hτSq.le))
    rw [show (κ ^ 2 / (1 - κ ^ 2 * contrast θ ^ 2))⁻¹ =
        κ⁻¹ ^ 2 - contrast θ ^ 2 by
      field_simp [hκ.ne', hden]
      ]
    rw [contraction_inv_eq_coth ε hε]
  · exact balancedRR_stationary ε hε
  · rw [balancedRR_variance_eq_sharp θ hθ hbalance ε hε,
      Vstar_balanced_eq_sharp_reciprocal θ hθ hbalance ε hε]

end CausalSmith.Stat.LdpAteEfficiencySurface
