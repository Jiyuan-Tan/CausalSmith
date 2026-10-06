module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotAdaptiveTransfer
public import Causalean.Mathlib.MeasureTheory.PartitionIntegral
public import Causalean.Stat.CLT.AsymptoticLinearity

/-! # Assembly lemmas for private-pilot attainment

This file supplies the finite pilot-prefix integral decomposition and the outer
asymptotic packaging used by the private-pilot theorem.  It deliberately does
not depend on the generic triangular-array limit theorem.
-/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

variable (select : TrialParameter → StaircaseWeight × ℝ × ℝ)

open MeasureTheory ProbabilityTheory Filter Causalean.Stat
open scoped ENNReal

/-- The observed coordinates lying in the pilot portion of a transcript. For [the displayed inputs and conditions](hyp:m), [the stated result](goal) follows. For [the displayed quantities and conditions](hyp:z), these specify the stated inputs. -/
def pilotObservedPrefix {n : ℕ} (m : ℕ → ℕ)
    (z : Transcript (pilotOutputFamily n)) :
    {i : Fin n // i.val < m n} → PilotOutput :=
  fun i => z i.1

/-- Under a finite product law with normalized one-coordinate weights, the
weighted expectation of a coordinate sum is the number of coordinates times
the one-coordinate weighted expectation. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:N,w,q,hw), these specify the stated inputs. -/
lemma finiteProduct_weighted_sum_expectation {A : Type*} [Fintype A]
    (N : ℕ) (w q : A → ℝ) (hw : ∑ a, w a = 1) :
    ∑ v : Fin N → A, (∏ j, w (v j)) * (∑ j, q (v j)) =
      (N : ℝ) * (∑ a, w a * q a) := by
  classical
  rw [show (∑ v : Fin N → A, (∏ j, w (v j)) * (∑ j, q (v j))) =
      ∑ v : Fin N → A, ∑ j, (∏ k, w (v k)) * q (v j) by
    apply Finset.sum_congr rfl
    intro v _
    exact Finset.mul_sum _ _ _]
  rw [Finset.sum_comm]
  calc
    (∑ j : Fin N, ∑ v : Fin N → A, (∏ k, w (v k)) * q (v j)) =
        ∑ j : Fin N, ∑ a, w a * q a := by
      apply Finset.sum_congr rfl
      intro j _
      let F : Fin N → A → ℝ := fun k a =>
        w a * if k = j then q a else 1
      calc
        (∑ v : Fin N → A, (∏ k, w (v k)) * q (v j)) =
            ∑ v : Fin N → A, ∏ k, F k (v k) := by
          apply Finset.sum_congr rfl
          intro v _
          rw [show (∏ k, F k (v k)) =
              (∏ k, w (v k)) * q (v j) by
            unfold F
            rw [Finset.prod_mul_distrib]
            simp]
        _ = ∏ k : Fin N, ∑ a, F k a := (Fintype.prod_sum F).symm
        _ = ∑ a, w a * q a := by
          rw [Finset.prod_eq_single j]
          · simp [F]
          · intro k _ hkj
            simp [F, hkj, hw]
          · simp
    _ = (N : ℝ) * (∑ a, w a * q a) := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- For a fixed pilot selection and a nonempty main row, the product-law expectation of the corrected main-sample estimator is centered at the true contrast. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hη,hε,hN), [the adaptive Main centered product sum](goal).

Under the stated assumptions, the adaptive Main centered product sum. -/
lemma adaptiveMain_centered_product_sum
    (θ η : TrialParameter) (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hη : InteriorMeans η) (hε : 0 < ε)
    (N : ℕ) (hN : 0 < N) :
    ∑ v : Fin N → Fin 14,
      (∏ j, adaptiveMainMass select θ η p ε (v j)) *
        (contrast η + (N : ℝ)⁻¹ *
          ∑ j, adaptiveSelectedScore select η p ε (v j) - contrast θ) = 0 := by
  let w : Fin 14 → ℝ := adaptiveMainMass select θ η p ε
  let q : Fin 14 → ℝ := adaptiveSelectedScore select η p ε
  have hw : ∑ s, w s = 1 := adaptiveMainMass_sum select θ η p ε hselect hp hη hε
  have hq : ∑ s, w s * q s = contrast θ - contrast η :=
    adaptiveSelectedScore_mean select θ η p ε hselect hp hη hε
  have hprod : ∑ v : Fin N → Fin 14, ∏ j, w (v j) = 1 := by
    rw [← Fintype.prod_sum]
    simp [hw]
  have hsum := finiteProduct_weighted_sum_expectation N w q hw
  change (∑ v : Fin N → Fin 14, (∏ j, w (v j)) *
    (contrast η + (N : ℝ)⁻¹ * ∑ j, q (v j) - contrast θ)) = 0
  calc
    _ = (contrast η - contrast θ) * (∑ v : Fin N → Fin 14, ∏ j, w (v j)) +
        (N : ℝ)⁻¹ *
          (∑ v : Fin N → Fin 14, (∏ j, w (v j)) * ∑ j, q (v j)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = (contrast η - contrast θ) +
        (N : ℝ)⁻¹ * ((N : ℝ) * (contrast θ - contrast η)) := by
      rw [hprod, hsum, hq]
      ring
    _ = 0 := by
      have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
      field_simp
      ring

/-- Split a finite sum at a bounded initial segment. For [the displayed inputs and conditions](hyp:hmn), [the stated result](goal) follows. For [the displayed quantities and conditions](hyp:f,g), these specify the stated inputs. -/
lemma fin_sum_split {M : Type*} [AddCommMonoid M] {m n : ℕ} (hmn : m ≤ n)
    (f : Fin m → M) (g : Fin (n - m) → M) :
    (∑ i : Fin n, if hi : i.val < m then f ⟨i.val, hi⟩
      else g ⟨i.val - m, by omega⟩) =
      (∑ j : Fin m, f j) + ∑ j : Fin (n - m), g j := by
  let e : Fin (m + (n - m)) ≃ Fin n := Fin.castOrderIso (Nat.add_sub_of_le hmn)
  rw [← e.sum_comp]
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    simp [e]
  · apply Finset.sum_congr rfl
    intro j _
    simp [e]

/-- On an encoded pilot/main transcript, `tauStar` is the pilot contrast plus the average of the selected main-release scores. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hε,hmn), [the tau Star pilot Adaptive Encode](goal).

Under the stated assumptions, the tau Star pilot Adaptive Encode. -/
lemma tauStar_pilotAdaptiveEncode
    (p ε : ℝ) (m : ℕ → ℕ) (hp : InteriorAssignment p) (hε : 0 < ε)
    {n : ℕ} (hmn : m n ≤ n) (u : Fin (m n) → Fin 4)
    (v : Fin (n - m n) → Fin 14) :
    tauStar p ε m (select) (pilotAdaptiveEncode hmn u v) =
      contrast (pilotAdaptivePrefixTheta p ε m hmn u) +
        ((n - m n : ℕ) : ℝ)⁻¹ *
          ∑ j, adaptiveSelectedScore select
            (pilotAdaptivePrefixTheta p ε m hmn u) p ε (v j) := by
  unfold tauStar
  rw [pilotTheta_pilotAdaptiveEncode p ε m hmn u v]
  dsimp only
  congr 1
  rw [show (∑ i : Fin n,
      if m n ≤ i.val then
        phiOutput (pilotAdaptivePrefixTheta p ε m hmn u) p ε
          (select) (pilotAdaptiveEncode hmn u v i)
      else 0) =
      ∑ i : Fin n, if hi : i.val < m n then (0 : ℝ)
        else adaptiveSelectedScore select (pilotAdaptivePrefixTheta p ε m hmn u)
          p ε (v ⟨i.val - m n, by omega⟩) by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val < m n
    · simp [hi]
    · have him : m n ≤ i.val := Nat.le_of_not_gt hi
      simp [hi, him, pilotAdaptiveEncode, phiOutput, adaptiveSelectedScore]]
  rw [fin_sum_split hmn (fun _ : Fin (m n) => (0 : ℝ))
    (fun j : Fin (n - m n) => adaptiveSelectedScore select
      (pilotAdaptivePrefixTheta p ε m hmn u) p ε (v j))]
  simp

/-- Conditional on a proper pilot prefix, the exact joint-law atom masses center the encoded main-row estimator at the true contrast. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hsub,hn), [the pilot Adaptive encoded centered sum](goal).

Under the stated assumptions, the pilot Adaptive encoded centered sum. -/
lemma pilotAdaptive_encoded_centered_sum
    (θ : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hsub : PilotSublinear m) (n : ℕ) (hn : 2 ≤ n)
    (u : Fin (m n) → Fin 4) :
    ∑ v : Fin (n - m n) → Fin 14,
      (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n
        {pilotAdaptiveEncode (Nat.le_of_lt (hsub.2 n hn).2) u v}).toReal *
      ((pilotEstimator p ε m select hselect hp hε).estimate n
        (pilotAdaptiveEncode (Nat.le_of_lt (hsub.2 n hn).2) u v) - contrast θ) = 0 := by
  let hmn : m n ≤ n := Nat.le_of_lt (hsub.2 n hn).2
  let η := pilotAdaptivePrefixTheta p ε m hmn u
  have hη : InteriorMeans η := by
    exact pilotTheta_interior p ε m
      (pilotAdaptiveEncode hmn u (fun _ => 0))
  have hN : 0 < n - m n := Nat.sub_pos_of_lt (hsub.2 n hn).2
  let a : ℝ := ∏ j : Fin (m n),
    ∑ x : Fin 4, piTheta θ p x * rrPilotProbability ε x (u j)
  have hpilot_nonneg (j : Fin (m n)) :
      0 ≤ ∑ x : Fin 4, piTheta θ p x * rrPilotProbability ε x (u j) := by
    apply Finset.sum_nonneg
    intro x _
    exact mul_nonneg (piTheta_pos_interior θ p hp hθ x).le (by
      unfold rrPilotProbability
      split_ifs <;> positivity)
  have hmain_nonneg (s : Fin 14) :
      0 ≤ adaptiveMainMass select θ η p ε s :=
    adaptiveMainMass_nonneg select θ η p ε hselect hp hθ hη hε s
  have hmass (v : Fin (n - m n) → Fin 14) :
      (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n
        {pilotAdaptiveEncode hmn u v}).toReal =
      a * ∏ j, adaptiveMainMass select θ η p ε (v j) := by
    have hpProd : 0 ≤ ∏ j : Fin (m n),
        ∑ x : Fin 4, piTheta θ p x * rrPilotProbability ε x (u j) :=
      Finset.prod_nonneg fun j _ => hpilot_nonneg j
    have hmProd : 0 ≤ ∏ j : Fin (n - m n),
        adaptiveMainMass select θ η p ε (v j) :=
      Finset.prod_nonneg fun j _ => hmain_nonneg (v j)
    rw [pilotAdaptive_joint_singleton select θ p ε m hselect hp hθ hε hmn u v]
    rw [ENNReal.toReal_mul]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => hpilot_nonneg j)]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => hmain_nonneg (v j))]
    rw [ENNReal.toReal_ofReal hpProd, ENNReal.toReal_ofReal hmProd]
  change (∑ v : Fin (n - m n) → Fin 14,
    (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n
      {pilotAdaptiveEncode hmn u v}).toReal *
    (tauStar p ε m (select) (pilotAdaptiveEncode hmn u v) -
      contrast θ)) = 0
  simp_rw [hmass, tauStar_pilotAdaptiveEncode select p ε m hp hε hmn u]
  change (∑ x : Fin (n - m n) → Fin 14,
      (a * ∏ j, adaptiveMainMass select θ η p ε (x j)) *
        (contrast η + ((n - m n : ℕ) : ℝ)⁻¹ *
          ∑ j, adaptiveSelectedScore select η p ε (x j) - contrast θ)) = 0
  rw [show (∑ x : Fin (n - m n) → Fin 14,
      (a * ∏ j, adaptiveMainMass select θ η p ε (x j)) *
        (contrast η + ((n - m n : ℕ) : ℝ)⁻¹ *
          ∑ j, adaptiveSelectedScore select η p ε (x j) - contrast θ)) =
      a * ∑ x : Fin (n - m n) → Fin 14,
        (∏ j, adaptiveMainMass select θ η p ε (x j)) *
          (contrast η + ((n - m n : ℕ) : ℝ)⁻¹ *
            ∑ j, adaptiveSelectedScore select η p ε (x j) - contrast θ) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring]
  rw [adaptiveMain_centered_product_sum select θ η p ε hselect hp hη hε (n - m n) hN]
  simp

/-- A transcript outside the correctly tagged pilot/main encoding has zero mass under the exact private-pilot law. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε,hmn,ht), [the pilot Adaptive singleton zero of not range](goal).

Under the stated assumptions, the pilot Adaptive singleton zero of not range. -/
lemma pilotAdaptive_singleton_zero_of_not_range
    (θ : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε)
    {n : ℕ} (hmn : m n ≤ n) (t : Transcript (pilotOutputFamily n))
    (ht : t ∉ Set.range fun uv :
      (Fin (m n) → Fin 4) × (Fin (n - m n) → Fin 14) =>
        pilotAdaptiveEncode hmn uv.1 uv.2) :
    transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n {t} = 0 := by
  have hwrong :
      (∃ i : Fin n, i.val < m n ∧ ∃ s : Fin 14, t i = Sum.inr s) ∨
      (∃ i : Fin n, m n ≤ i.val ∧ ∃ k : Fin 4, t i = Sum.inl k) := by
    by_contra hnone
    push Not at hnone
    let u : Fin (m n) → Fin 4 := fun j =>
      Sum.elim id (fun _ => 0) (t (Fin.castLE hmn j) : PilotOutput)
    let v : Fin (n - m n) → Fin 14 := fun j =>
      Sum.elim (fun _ => 0) id
        (t ⟨m n + j.val, by omega⟩ : PilotOutput)
    apply ht
    refine ⟨(u, v), ?_⟩
    funext i
    by_cases hi : i.val < m n
    · cases hti : t i with
      | inl k => simp [pilotAdaptiveEncode, hi, u, hti]
      | inr s => exact False.elim (hnone.1 i hi s hti)
    · have him : m n ≤ i.val := Nat.le_of_not_gt hi
      have hjlt : i.val - m n < n - m n := by omega
      have hidx : (⟨m n + (⟨i.val - m n, hjlt⟩ : Fin (n - m n)).val,
          by omega⟩ : Fin n) = i := Fin.ext (Nat.add_sub_of_le him)
      cases hti : t i with
      | inl k => exact False.elim (hnone.2 i him k hti)
      | inr s =>
          have htidx : t ⟨m n + (⟨i.val - m n, hjlt⟩ : Fin (n - m n)).val,
              by omega⟩ = Sum.inr s := by rw [hidx]; exact hti
          simp [pilotAdaptiveEncode, hi, v, htidx]
  unfold transcriptLaw
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul]
  apply Finset.sum_eq_zero
  intro x _
  suffices (pilotEstimator p ε m select hselect hp hε).transcript n x {t} = 0 by simp [this]
  change finiteSequenceTranscript
    (pilotProtocol p ε m (select) n) x {t} = 0
  rw [finiteSequenceTranscript_singleton_apply]
  · rcases hwrong with ⟨i, hi, s, hs⟩ | ⟨i, hi, k, hk⟩
    · apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [hs]
      exact pilotProtocol_pilot_wrongTag select p ε m hselect hp hε i hi (x i)
        (fun j => t j.1) s
    · apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [hk]
      exact pilotProtocol_main_wrongTag select p ε m hselect hp hε i hi (x i)
        (fun j => t j.1) k
  · exact (pilotProtocol_private p ε m select hselect hp hε n).1

/-- The joint pilot/main transcript encoding is injective. For [the displayed inputs and conditions](hyp:hmn), [the stated result](goal) follows. -/
lemma pilotAdaptiveEncode_pair_injective {m n : ℕ} (hmn : m ≤ n) :
    Function.Injective (fun uv : (Fin m → Fin 4) × (Fin (n - m) → Fin 14) =>
      pilotAdaptiveEncode hmn uv.1 uv.2) := by
  intro uv uv' h
  apply Prod.ext
  · funext j
    have hj := congrFun h (Fin.castLE hmn j)
    dsimp only at hj
    rw [pilotAdaptiveEncode_pilot hmn uv.1 uv.2 j,
      pilotAdaptiveEncode_pilot hmn uv'.1 uv'.2 j] at hj
    exact Sum.inl_injective hj
  · funext j
    have hj := congrFun h (⟨m + j.val, by omega⟩ : Fin n)
    dsimp only at hj
    rw [pilotAdaptiveEncode_main hmn uv.1 uv.2 j,
      pilotAdaptiveEncode_main hmn uv'.1 uv'.2 j] at hj
    exact Sum.inr_injective hj

/-- A finite sum supported on an injectively parameterized range can be
reindexed by the parameters. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:e,he,F,hzero), these specify the stated inputs. -/
lemma sum_eq_sum_image_of_zero_off_range
    {A Ω M : Type*} [Fintype A] [Fintype Ω] [AddCommMonoid M]
    (e : A → Ω) (he : Function.Injective e) (F : Ω → M)
    (hzero : ∀ x, x ∉ Set.range e → F x = 0) :
    ∑ x : Ω, F x = ∑ a : A, F (e a) := by
  classical
  rw [← Finset.sum_image (fun a _ b _ hab => he hab)]
  symm
  apply Finset.sum_subset (by simp)
  intro x _ hx
  apply hzero x
  simpa using hx

/-- The centered private-pilot estimator has integral zero on every observed pilot-prefix fiber. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hsub,hn,r), [the pilot prefix cell centered](goal).

Under the stated assumptions, the pilot prefix cell centered. -/
lemma pilot_prefix_cell_centered
    (θ : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hsub : PilotSublinear m) (n : ℕ) (hn : 2 ≤ n)
    (r : {i : Fin n // i.val < m n} → PilotOutput) :
    (∫ z in (pilotObservedPrefix (n := n) m) ⁻¹' {r},
      ((pilotEstimator p ε m select hselect hp hε).estimate n z - contrast θ)
      ∂transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n) = 0 := by
  classical
  let μ := transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n
  let H := pilotObservedPrefix (n := n) m
  let g : Transcript (pilotOutputFamily n) → ℝ := fun z =>
    (pilotEstimator p ε m select hselect hp hε).estimate n z - contrast θ
  let hmn : m n ≤ n := Nat.le_of_lt (hsub.2 n hn).2
  let e := fun uv : (Fin (m n) → Fin 4) × (Fin (n - m n) → Fin 14) =>
    pilotAdaptiveEncode hmn uv.1 uv.2
  letI : IsProbabilityMeasure μ :=
    transcriptLaw_isProbability (pilotEstimator p ε m select hselect hp hε) θ p hp hθ n
  have hprefix (u : Fin (m n) → Fin 4) (v : Fin (n - m n) → Fin 14) :
      H (e (u, v)) = fun i => Sum.inl (u ⟨i.val, i.property⟩) := by
    funext i
    change (if hi : i.val < m n then Sum.inl (u ⟨i.val, hi⟩)
      else Sum.inr (v ⟨i.val - m n, by omega⟩)) = _
    simp [i.property]
  rw [MeasureTheory.integral_fintype Integrable.of_finite]
  change (∑ z, (μ.restrict (H ⁻¹' {r}) {z}).toReal * g z) = 0
  rw [sum_eq_sum_image_of_zero_off_range e
    (pilotAdaptiveEncode_pair_injective hmn)]
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_eq_zero
    intro u _
    by_cases hur : H (e (u, fun _ => 0)) = r
    · have huv (v : Fin (n - m n) → Fin 14) : H (e (u, v)) = r := by
        calc
          H (e (u, v)) = (fun i => Sum.inl (u ⟨i.val, i.property⟩)) := hprefix u v
          _ = H (e (u, fun _ => 0)) := (hprefix u (fun _ => 0)).symm
          _ = r := hur
      simp_rw [show ∀ v : Fin (n - m n) → Fin 14,
          (μ.restrict (H ⁻¹' {r}) {e (u, v)}).toReal =
            (μ {e (u, v)}).toReal by
        intro v
        rw [MeasureTheory.Measure.restrict_apply (measurableSet_singleton _)]
        simp [huv v]]
      exact pilotAdaptive_encoded_centered_sum select θ p ε m hselect hp hθ hε hsub n hn u
    · have huv (v : Fin (n - m n) → Fin 14) : H (e (u, v)) ≠ r := by
        intro h
        apply hur
        calc
          H (e (u, fun _ => 0)) =
              (fun i => Sum.inl (u ⟨i.val, i.property⟩)) := hprefix u (fun _ => 0)
          _ = H (e (u, v)) := (hprefix u v).symm
          _ = r := h
      apply Finset.sum_eq_zero
      intro v _
      rw [MeasureTheory.Measure.restrict_apply (measurableSet_singleton _)]
      simp [huv v]
  · intro t ht
    have hzero := pilotAdaptive_singleton_zero_of_not_range
      select θ p ε m hselect hp hε hmn t ht
    rw [MeasureTheory.Measure.restrict_apply (measurableSet_singleton _)]
    have hsubsingleton : {t} ∩ H ⁻¹' {r} ⊆ ({t} : Set _) := Set.inter_subset_left
    have hz : μ ({t} ∩ H ⁻¹' {r}) = 0 := measure_mono_null hsubsingleton hzero
    simp [hz]

/-- A Wald pivot with an explicit zero-variance fallback. The fallback makes the closed-interval event exactly equivalent to the unstudentized Wald event, including samples on which the variance estimate is zero. [The wald Fallback Pivot](goal) is determined by [the displayed parameters](hyp:cutoff,n,e,v). -/
noncomputable def waldFallbackPivot (cutoff : ℝ) (n : ℕ) (e v : ℝ) : ℝ :=
  if v = 0 then if e = 0 then 0 else cutoff + 1
  else Real.sqrt n * e / Real.sqrt v

/-- Membership of the fallback pivot in the symmetric cutoff interval is
exactly the corresponding Wald inequality. For [the displayed inputs and conditions](hyp:hcutoff,hn), [the stated result](goal) follows. For [the displayed quantities and conditions](hyp:hv), these specify the stated inputs. -/
lemma mem_Icc_waldFallbackPivot_iff
    {cutoff : ℝ} (hcutoff : 0 < cutoff) {n : ℕ} (hn : 0 < n)
    {e v : ℝ} (hv : 0 ≤ v) :
    waldFallbackPivot cutoff n e v ∈ Set.Icc (-cutoff) cutoff ↔
      |e| ≤ cutoff * Real.sqrt (v / n) := by
  by_cases hv0 : v = 0
  · subst v
    by_cases he0 : e = 0
    · subst e
      simp [waldFallbackPivot, hcutoff.le]
    · have habs : 0 < |e| := abs_pos.mpr he0
      simp [waldFallbackPivot, he0, not_le_of_gt habs]
  · have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnreal
    have hsv : 0 < Real.sqrt v := Real.sqrt_pos.2 hvpos
    rw [show waldFallbackPivot cutoff n e v =
        Real.sqrt n * e / Real.sqrt v by simp [waldFallbackPivot, hv0]]
    rw [show (Real.sqrt n * e / Real.sqrt v ∈ Set.Icc (-cutoff) cutoff) ↔
        |Real.sqrt n * e / Real.sqrt v| ≤ cutoff by simp [abs_le]]
    rw [Real.sqrt_div hv]
    simp only [abs_div, abs_mul]
    rw [abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [div_le_iff₀ hsv]
    rw [show cutoff * (Real.sqrt v / Real.sqrt (n : ℝ)) =
      (cutoff * Real.sqrt v) / Real.sqrt (n : ℝ) by ring]
    rw [le_div_iff₀ hsn]
    ring_nf

/-- The main-sample empirical variance is nonnegative on every transcript. For [the displayed inputs and conditions](hyp:p,m), [the stated result](goal) follows. For [the displayed quantities and conditions](hyp:select,z), these specify the stated inputs. -/
lemma pilotVhatStar_nonneg (p ε : ℝ) (m : ℕ → ℕ)
    (select : TrialParameter → StaircaseWeight × ℝ × ℝ)
    {n : ℕ} (z : Transcript (pilotOutputFamily n)) :
    0 ≤ VhatStar p ε m select z := by
  unfold VhatStar
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun i _ => by split_ifs <;> positivity)

/-- The fallback-studentized private-pilot estimation error. [The pilot Wald Pivot](goal) is determined by [the displayed parameters](hyp:select,cutoff,θ,p,ε,m,hselect,hp,hε,n,z). -/
noncomputable def pilotWaldPivot
    (cutoff : ℝ) (θ : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) (n : ℕ)
    (z : Transcript (pilotOutputFamily n)) : ℝ :=
  waldFallbackPivot cutoff n
    ((pilotEstimator p ε m select hselect hp hε).estimate n z - contrast θ)
    (VhatStar p ε m (select) z)

/-- At every positive sample size, the private-pilot Wald coverage event is the symmetric closed-interval event for the fallback pivot. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hcutoff,hselect,hp,hε,hn), [the pilot wald event eq](goal).

Under the stated assumptions, the pilot wald event eq. -/
lemma pilot_wald_event_eq
    (cutoff : ℝ) (hcutoff : 0 < cutoff)
    (θ : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) (n : ℕ) (hn : 0 < n) :
    {z : Transcript (pilotOutputFamily n) |
      |(pilotEstimator p ε m select hselect hp hε).estimate n z - contrast θ| ≤
        cutoff * Real.sqrt
          (VhatStar p ε m (select) z / n)} =
    {z | pilotWaldPivot select cutoff θ p ε m hselect hp hε n z ∈
      Set.Icc (-cutoff) cutoff} := by
  ext z
  exact (mem_Icc_waldFallbackPivot_iff hcutoff hn
    (pilotVhatStar_nonneg p ε m (select) z)).symm

/-- Convergence of the fallback-pivot interval probability transfers directly to the private-pilot Wald coverage probability. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hcutoff,hselect,hp,hε,hpivot), [the pilot wald coverage of pivot Icc](goal).

Under the stated assumptions, the pilot wald coverage of pivot Icc. -/
lemma pilot_wald_coverage_of_pivot_Icc
    (cutoff : ℝ) (hcutoff : 0 < cutoff)
    (θ : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) (L : ℝ)
    (hpivot : Tendsto (fun n =>
      ((transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n)
        {z | pilotWaldPivot select cutoff θ p ε m hselect hp hε n z ∈
          Set.Icc (-cutoff) cutoff}).toReal) atTop (nhds L)) :
    Tendsto (fun n =>
      ((transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n)
        {z | |(pilotEstimator p ε m select hselect hp hε).estimate n z - contrast θ| ≤
          cutoff * Real.sqrt
            (VhatStar p ε m (select) z / n)}).toReal)
      atTop (nhds L) := by
  refine hpivot.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  rw [pilot_wald_event_eq select cutoff hcutoff θ p ε m hselect hp hε n hn]

/-- If a centered integrand has integral zero on every finite pilot-prefix
fiber, multiplying it by any statistic determined by the pilot prefix remains
integrable and has integral zero. For [the displayed inputs and conditions](hyp:m), [the stated result](goal) follows. For [the displayed quantities and conditions](hyp:g,f,hcenter,hadapt), these specify the stated inputs. -/
lemma pilot_adapted_centered_integral {n : ℕ} (m : ℕ → ℕ)
    (μ : Measure (Transcript (pilotOutputFamily n))) [IsFiniteMeasure μ]
    (g f : Transcript (pilotOutputFamily n) → ℝ)
    (hcenter : ∀ u, ∫ z in
      (pilotObservedPrefix (n := n) m) ⁻¹' {u}, g z ∂μ = 0)
    (hadapt : ∀ z z',
      (∀ i : Fin n, i.val < m n → z i = z' i) → f z = f z') :
    Integrable (fun z => g z * f z) μ ∧
      (∫ z, g z * f z ∂μ) = 0 := by
  classical
  let extend : ({i : Fin n // i.val < m n} → PilotOutput) →
      Transcript (pilotOutputFamily n) := fun u i =>
    if hi : i.val < m n then u ⟨i, hi⟩ else Sum.inl 0
  let c : ({i : Fin n // i.val < m n} → PilotOutput) → ℝ :=
    fun u => f (extend u)
  have hf_eq : ∀ z, f z = c (pilotObservedPrefix m z) := by
    intro z
    apply hadapt z
    intro i hi
    simp [extend, pilotObservedPrefix, hi]
  constructor
  · exact Integrable.of_finite
  · have hfiber : ∀ u : ({i : Fin n // i.val < m n} → PilotOutput),
        MeasurableSet
          ((pilotObservedPrefix (n := n) m) ⁻¹' {u}) := by
      intro u
      exact (measurable_of_finite _)
        (measurableSet_singleton u)
    have hdecomp := Causalean.Mathlib.MeasureTheory.integral_cellConst_mul
      (μ := μ) (H := pilotObservedPrefix (n := n) m)
      hfiber c (f := g) (hf := Integrable.of_finite)
    rw [show (∫ z, g z * f z ∂μ) =
        ∫ z, c (pilotObservedPrefix m z) • g z ∂μ by
      apply integral_congr_ae
      filter_upwards with z
      rw [hf_eq z]
      simp [mul_comm]]
    rw [hdecomp]
    simp [hcenter]

/-- Fiberwise centering of the pilot estimator implies the full conditional unbiasedness clause against every bounded measurable pilot statistic. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hcenter), [the pilot conditional unbiasedness of prefix cells](goal).

Under the stated assumptions, the pilot conditional unbiasedness of prefix cells. -/
lemma pilot_conditional_unbiasedness_of_prefix_cells
    (θ : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hcenter : ∀ n ≥ 2,
      ∀ u : ({i : Fin n // i.val < m n} → PilotOutput),
        (∫ z in (pilotObservedPrefix (n := n) m) ⁻¹' {u},
          ((pilotEstimator p ε m select hselect hp hε).estimate n z - contrast θ)
          ∂transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n) = 0) :
    ∀ n ≥ 2, ∀ f : Transcript (pilotOutputFamily n) → ℝ,
      Measurable f →
      (∃ C : ℝ, ∀ z, |f z| ≤ C) →
      (∀ z z', (∀ i : Fin n, i.val < m n → z i = z' i) → f z = f z') →
      Integrable (fun z =>
        ((pilotEstimator p ε m select hselect hp hε).estimate n z - contrast θ) * f z)
        (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n) ∧
      (∫ z, ((pilotEstimator p ε m select hselect hp hε).estimate n z - contrast θ) * f z
        ∂transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n) = 0 := by
  intro n hn f _ _ hadapt
  haveI : IsProbabilityMeasure
      (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n) :=
    transcriptLaw_isProbability _ θ p hp hθ n
  exact pilot_adapted_centered_integral m
    (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n)
    (fun z => (pilotEstimator p ε m select hselect hp hε).estimate n z - contrast θ)
    f (hcenter n hn) hadapt

/-- The private-pilot estimator satisfies the headline conditional unbiasedness clause under the stated sublinear pilot condition. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hsub), [the pilot conditional unbiasedness](goal).

Under the stated assumptions, the pilot conditional unbiasedness. -/
lemma pilot_conditional_unbiasedness
    (θ : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hsub : PilotSublinear m) :
    ∀ n ≥ 2, ∀ f : Transcript (pilotOutputFamily n) → ℝ,
      Measurable f →
      (∃ C : ℝ, ∀ z, |f z| ≤ C) →
      (∀ z z', (∀ i : Fin n, i.val < m n → z i = z' i) → f z = f z') →
      Integrable (fun z =>
        ((pilotEstimator p ε m select hselect hp hε).estimate n z - contrast θ) * f z)
        (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n) ∧
      (∫ z, ((pilotEstimator p ε m select hselect hp hε).estimate n z - contrast θ) * f z
        ∂transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n) = 0 := by
  apply pilot_conditional_unbiasedness_of_prefix_cells select θ p ε m hselect hp hθ hε
  intro n hn r
  exact pilot_prefix_cell_centered select θ p ε m hselect hp hθ hε hsub n hn r

/-- A centered Gaussian law has a finite second moment in the extended-real
form required by `RegularProcedure`. For [the displayed inputs and conditions](hyp:v), [the stated result](goal) follows. -/
lemma gaussian_second_lintegral_lt_top (v : ℝ) :
    (∫⁻ u, ENNReal.ofReal (u ^ 2) ∂gaussianMeasure 0 v) < ⊤ := by
  have hmem : MemLp id 2 (gaussianMeasure 0 v) := by
    unfold gaussianMeasure
    exact ProbabilityTheory.memLp_id_gaussianReal 2
  exact hmem.integrable_sq.lintegral_lt_top

/-- A weak local Gaussian limit and the defining uniform squared-tail condition
assemble into the regular-procedure interface. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,p,v,hweak,htails), these specify the stated inputs. -/
lemma regular_of_weakLocalLimit_and_uniformTails
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)]
    {ε : ℝ} (P : ProcedureSequence Z ε)
    (θ : TrialParameter) (p v : ℝ)
    (hweak : WeakLocalLimit P θ p (gaussianMeasure 0 v))
    (htails : ∀ H : ℝ, 0 < H →
      Tendsto (fun M : ℕ =>
        Filter.limsup (fun n =>
          sSup {u : ℝ≥0∞ | ∃ h ∈ localIndexSet θ n H,
            u = ∫⁻ z, ENNReal.ofReal
              ((scaledError P θ h n z) ^ 2 *
                if M < |scaledError P θ h n z| then 1 else 0)
              ∂transcriptLaw P (localAlternative θ h n) p n})
          atTop) atTop (nhds 0)) :
    RegularProcedure P θ p := by
  refine ⟨gaussianMeasure 0 v, inferInstance, ?_, hweak, htails⟩
  exact gaussian_second_lintegral_lt_top v

/-- The pilot weak limit, plug-in variance consistency, and uniform squared tails package the three asymptotic interfaces consumed together by the attainment theorem. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε,hweak,hvhat,htails), [the pilot limit variance regular of core](goal).

Under the stated assumptions, the pilot limit variance regular of core. -/
-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
lemma pilot_limit_variance_regular_of_core
    (θ : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε)
    (hweak : WeakLocalLimit (pilotEstimator p ε m select hselect hp hε) θ p
      (gaussianMeasure 0 (Vstar θ p ε)))
    (hvhat : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n =>
        (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n)
          {z | δ < |VhatStar p ε m (select) z -
            Vstar θ p ε|}) atTop (nhds 0))
    (htails : ∀ H : ℝ, 0 < H →
      Tendsto (fun M : ℕ =>
        Filter.limsup (fun n =>
          sSup {u : ℝ≥0∞ | ∃ h ∈ localIndexSet θ n H,
            u = ∫⁻ z, ENNReal.ofReal
              ((scaledError (pilotEstimator p ε m select hselect hp hε) θ h n z) ^ 2 *
                if M < |scaledError (pilotEstimator p ε m select hselect hp hε) θ h n z|
                then 1 else 0)
              ∂transcriptLaw (pilotEstimator p ε m select hselect hp hε)
                (localAlternative θ h n) p n})
          atTop) atTop (nhds 0)) :
    WeakLocalLimit (pilotEstimator p ε m select hselect hp hε) θ p
        (gaussianMeasure 0 (Vstar θ p ε)) ∧
      (∀ δ : ℝ, 0 < δ →
        Tendsto (fun n =>
          (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n)
            {z | δ < |VhatStar p ε m (select) z -
              Vstar θ p ε|}) atTop (nhds 0)) ∧
      RegularProcedure (pilotEstimator p ε m select hselect hp hε) θ p := by
  exact ⟨hweak, hvhat,
    regular_of_weakLocalLimit_and_uniformTails
      (pilotEstimator p ε m select hselect hp hε) θ p (Vstar θ p ε) hweak htails⟩

/-- If every positive-radius local worst-risk sequence has the same liminf,
the outer radius supremum in `localAsymptoticRisk` equals that value. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,p,v,hlim), these specify the stated inputs. -/
lemma localAsymptoticRisk_eq_of_liminf_localWorstRisk
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)]
    {ε : ℝ} (P : ProcedureSequence Z ε)
    (θ : TrialParameter) (p : ℝ) (v : ℝ≥0∞)
    (hlim : ∀ H : ℝ, 0 < H →
      Filter.liminf (fun n => localWorstRisk P θ p H n) atTop = v) :
    localAsymptoticRisk P θ p = v := by
  unfold localAsymptoticRisk
  apply le_antisymm
  · apply sSup_le
    intro u hu
    obtain ⟨H, hH, rfl⟩ := hu
    exact le_of_eq (hlim H hH)
  · apply le_sSup
    exact ⟨1, by norm_num, (hlim 1 (by norm_num)).symm⟩

end CausalSmith.Stat.LdpAteEfficiencySurface
