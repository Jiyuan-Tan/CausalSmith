module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotMoments
public import Causalean.Stat.Limit.WLLN
public import Causalean.Stat.Sample.PiTransport

/-! # Finite-prefix laws for the randomized-response pilot -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

variable (select : TrialParameter → StaircaseWeight × ℝ × ℝ)

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Causalean.Mathlib.Probability.Kernel.FiniteSequence

/-- the fin prod ite lt assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hℓn), [the fin prod ite lt](goal).

Under the stated assumptions, the fin prod ite lt. -/
lemma fin_prod_ite_lt {M : Type*} [CommMonoid M] {n ℓ : ℕ}
    (hℓn : ℓ ≤ n) (f : Fin ℓ → M) :
    ∏ i : Fin n, (if hi : i.val < ℓ then f ⟨i.val, hi⟩ else 1) =
      ∏ j : Fin ℓ, f j := by
  let g : Fin n → M := fun i =>
    if hi : i.val < ℓ then f ⟨i.val, hi⟩ else 1
  change (∏ i : Fin n, g i) = _
  have hfilter : (∏ i : Fin n, g i) =
      ∏ i ∈ (Finset.univ.filter fun i : Fin n => i.val < ℓ), g i := by
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i.val < ℓ <;> simp [g, hi]
  rw [hfilter]
  symm
  apply Finset.prod_bij (fun j _ => Fin.castLE hℓn j)
  · intro j _
    simp
  · intro a _ b _ hab
    exact Fin.castLE_injective hℓn hab
  · intro i hi
    have hil : i.val < ℓ := (Finset.mem_filter.mp hi).2
    exact ⟨⟨i.val, hil⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro j _
    simp [g]

/-- the fin sum ite lt assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hℓn), [the fin sum ite lt](goal).

Under the stated assumptions, the fin sum ite lt. -/
lemma fin_sum_ite_lt {M : Type*} [AddCommMonoid M] {n ℓ : ℕ}
    (hℓn : ℓ ≤ n) (f : Fin ℓ → M) :
    ∑ i : Fin n, (if hi : i.val < ℓ then f ⟨i.val, hi⟩ else 0) =
      ∑ j : Fin ℓ, f j := by
  let g : Fin n → M := fun i =>
    if hi : i.val < ℓ then f ⟨i.val, hi⟩ else 0
  change (∑ i : Fin n, g i) = _
  have hfilter : (∑ i : Fin n, g i) =
      ∑ i ∈ (Finset.univ.filter fun i : Fin n => i.val < ℓ), g i := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val < ℓ <;> simp [g, hi]
  rw [hfilter]
  symm
  apply Finset.sum_bij (fun j _ => Fin.castLE hℓn j)
  · intro j _
    simp
  · intro a _ b _ hab
    exact Fin.castLE_injective hℓn hab
  · intro i hi
    have hil : i.val < ℓ := (Finset.mem_filter.mp hi).2
    exact ⟨⟨i.val, hil⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro j _
    simp [g]

/-- Under [the supplied quantities and conditions](hyp:j,k), [the rr pilot kernel singleton assertion](goal) holds. -/
lemma rrPilotKernel_singleton (ε : ℝ) (j k : Fin 4) :
    rrPilotKernel ε j {k} = ENNReal.ofReal (rrPilotProbability ε j k) := by
  change (Measure.count.withDensity
    (fun l : Fin 4 => ENNReal.ofReal (rrPilotProbability ε j l))) {k} = _
  rw [withDensity_apply _ (measurableSet_singleton k)]
  simp

/-- Under [the supplied quantities and conditions](hyp:p), [the pi theta sum eq one assertion](goal) holds. -/
lemma piTheta_sum_eq_one (θ : TrialParameter) (p : ℝ) :
    ∑ j : Fin 4, piTheta θ p j = 1 := by
  have hpi0 : piTheta θ p 0 = controlProb p * (1 - θ 0) := rfl
  have hpi1 : piTheta θ p 1 = controlProb p * θ 0 := rfl
  have hpi2 : piTheta θ p 2 = p * (1 - θ 1) := rfl
  have hpi3 : piTheta θ p 3 = p * θ 1 := rfl
  simp [Fin.sum_univ_four, hpi0, hpi1, hpi2, hpi3, controlProb]
  ring

/-- Under [the supplied quantities and conditions](hyp:p,n), [the input path probability sum eq one assertion](goal) holds. -/
lemma inputPathProbability_sum_eq_one (θ : TrialParameter) (p : ℝ) (n : ℕ) :
    ∑ x : Fin n → Fin 4, inputPathProbability θ p x = 1 := by
  change (∑ x : Fin n → Fin 4, ∏ i : Fin n, piTheta θ p (x i)) = 1
  calc
    (∑ x : Fin n → Fin 4, ∏ i : Fin n, piTheta θ p (x i)) =
        ∏ _i : Fin n, ∑ a : Fin 4, piTheta θ p a :=
      (Fintype.prod_sum (fun _i : Fin n => fun a : Fin 4 => piTheta θ p a)).symm
    _ = 1 := by simp [piTheta_sum_eq_one]

/-- the transcript law is probability assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the transcript Law is Probability](goal).

Under the stated assumptions, the transcript Law is Probability. -/
lemma transcriptLaw_isProbability {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (n : ℕ) :
    IsProbabilityMeasure (transcriptLaw P θ p n) := by
  rw [isProbabilityMeasure_iff]
  unfold transcriptLaw
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul]
  have hpath (x : Fin n → Fin 4) : 0 ≤ inputPathProbability θ p x := by
    unfold inputPathProbability
    exact Finset.prod_nonneg fun i _ =>
      (piTheta_pos_interior θ p hp hθ (x i)).le
  rw [show (∑ x : Fin n → Fin 4,
      ENNReal.ofReal (inputPathProbability θ p x) *
        P.transcript n x Set.univ) =
      ∑ x : Fin n → Fin 4,
        ENNReal.ofReal (inputPathProbability θ p x) by
    apply Finset.sum_congr rfl
    intro x _
    rw [(P.factorizes n x).1.measure_univ, mul_one]]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · rw [inputPathProbability_sum_eq_one]
    simp
  · intro x _
    exact hpath x

/-- Marginalizing independent private inputs turns the deterministic-path pilot prefix product into the product of calibrated RR marginals. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hℓn), [the input Path prefix rr sum](goal).

Under the stated assumptions, the input Path prefix rr sum. -/
lemma inputPath_prefix_rr_sum (θ : TrialParameter) (p ε : ℝ)
    {n ℓ : ℕ} (hℓn : ℓ ≤ n) (u : Fin ℓ → Fin 4) :
    ∑ x : Fin n → Fin 4, inputPathProbability θ p x *
        (∏ j : Fin ℓ,
          rrPilotProbability ε (x (Fin.castLE hℓn j)) (u j)) =
      ∏ j : Fin ℓ,
        (∑ a : Fin 4, piTheta θ p a * rrPilotProbability ε a (u j)) := by
  let F : (i : Fin n) → Fin 4 → ℝ := fun i a =>
    piTheta θ p a *
      if hi : i.val < ℓ then rrPilotProbability ε a (u ⟨i.val, hi⟩) else 1
  calc
    (∑ x : Fin n → Fin 4, inputPathProbability θ p x *
        (∏ j : Fin ℓ,
          rrPilotProbability ε (x (Fin.castLE hℓn j)) (u j))) =
        ∑ x : Fin n → Fin 4, ∏ i : Fin n, F i (x i) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [show inputPathProbability θ p x =
            ∏ i : Fin n, piTheta θ p (x i) by rfl]
          rw [← fin_prod_ite_lt hℓn (fun j =>
            rrPilotProbability ε (x (Fin.castLE hℓn j)) (u j))]
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro i _
          simp only [F]
          split_ifs with hi <;> rfl
    _ = ∏ i : Fin n, ∑ a : Fin 4, F i a := (Fintype.prod_sum F).symm
    _ = ∏ i : Fin n, (if hi : i.val < ℓ then
          ∑ a : Fin 4, piTheta θ p a * rrPilotProbability ε a (u ⟨i.val, hi⟩)
        else 1) := by
          apply Finset.prod_congr rfl
          intro i _
          simp only [F]
          split_ifs with hi
          · rfl
          · simp [piTheta_sum_eq_one]
    _ = _ := fin_prod_ite_lt hℓn (fun j =>
      ∑ a : Fin 4, piTheta θ p a * rrPilotProbability ε a (u j))

/-- Under [the supplied quantities and conditions](hyp:p), [the rr pilot marginal sum eq one assertion](goal) holds. -/
lemma rrPilot_marginal_sum_eq_one (θ : TrialParameter) (p ε : ℝ) :
    ∑ k : Fin 4, (∑ a : Fin 4,
      piTheta θ p a * rrPilotProbability ε a k) = 1 := by
  simp_rw [rrPilot_marginal_probability]
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum,
    piTheta_sum_eq_one]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.cast_ofNat]
  field_simp [ne_of_gt (by positivity : 0 < Real.exp ε + 3)]
  ring

/-- The one-coordinate randomized-response marginal after integrating out the private four-cell input. For the displayed inputs and conditions, the stated result follows. [The rr Pilot Marginal](goal) is determined by [the displayed parameters](hyp:θ,p,ε). -/
def rrPilotMarginal (θ : TrialParameter) (p ε : ℝ) : Measure (Fin 4) :=
  Measure.count.withDensity fun k => ENNReal.ofReal
    (∑ a : Fin 4, piTheta θ p a * rrPilotProbability ε a k)

/-- Under [the supplied quantities and conditions](hyp:p,k), [the rr pilot marginal singleton assertion](goal) holds. -/
lemma rrPilotMarginal_singleton (θ : TrialParameter) (p ε : ℝ) (k : Fin 4) :
    rrPilotMarginal θ p ε {k} = ENNReal.ofReal
      (∑ a : Fin 4, piTheta θ p a * rrPilotProbability ε a k) := by
  rw [rrPilotMarginal, withDensity_apply _ (measurableSet_singleton k)]
  simp

/-- Under the supplied quantities and conditions, the rr pilot marginal is probability assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the rr Pilot Marginal is Probability](goal).

Under the stated assumptions, the rr Pilot Marginal is Probability. -/
lemma rrPilotMarginal_isProbability (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) :
    IsProbabilityMeasure (rrPilotMarginal θ p ε) := by
  rw [isProbabilityMeasure_iff, rrPilotMarginal, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ, lintegral_count, tsum_fintype,
    ← ENNReal.ofReal_sum_of_nonneg]
  · rw [rrPilot_marginal_sum_eq_one]
    simp
  · intro k _
    exact Finset.sum_nonneg fun a _ => mul_nonneg
      (piTheta_pos_interior θ p hp hθ a).le (by
        unfold rrPilotProbability
        split_ifs <;> positivity)

/-- For a deterministic private-input path, every initial segment lying wholly inside the pilot has the product randomized-response atom probability. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε,hℓn,hℓm), [the pilot Prefix component singleton](goal).

Under the stated assumptions, the pilot Prefix component singleton. -/
lemma pilotPrefix_component_singleton (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε)
    {n ℓ : ℕ} (hℓn : ℓ ≤ n) (hℓm : ℓ ≤ m n)
    (x : Fin n → Fin 4) (u : Fin ℓ → Fin 4) :
    prefixLaw
        (finiteSequenceKernel
          (pilotProtocol p ε m (select) n)) x ℓ hℓn
        {fun j => (Sum.inl (u j) : PilotOutput)} =
      ∏ j : Fin ℓ, ENNReal.ofReal
        (rrPilotProbability ε (x (Fin.castLE hℓn j)) (u j)) := by
  induction ℓ with
  | zero =>
      have he : ({fun j : Fin 0 => (Sum.inl (u j) : PilotOutput)} :
          Set (History (pilotOutputFamily n) 0 hℓn)) = Set.univ := by
        ext v
        have hv : v = fun j : Fin 0 => (Sum.inl (u j) : PilotOutput) := by
          funext j
          exact j.elim0
        constructor <;> intro
        · exact Set.mem_univ _
        · exact Set.mem_singleton_iff.mpr hv
      rw [he]
      have hQ : ∀ i, IsMarkovKernel
          (finiteSequenceKernel
            (pilotProtocol p ε m (select) n) i) := by
        intro i
        letI : IsMarkovKernel
            (pilotProtocol p ε m (select) n i) :=
          (pilotProtocol_private p ε m select hselect hp hε n).1 i
        dsimp [finiteSequenceKernel]
        infer_instance
      haveI := isProbabilityMeasure_prefixLaw
        (finiteSequenceKernel
          (pilotProtocol p ε m (select) n)) hQ x 0 hℓn
      simp
  | succ r ih =>
      have hrn : r ≤ n := Nat.le_of_succ_le hℓn
      have hrm : r ≤ m n := Nat.le_trans (Nat.le_succ r) hℓm
      have hQ : ∀ i, IsMarkovKernel
          (finiteSequenceKernel
            (pilotProtocol p ε m (select) n) i) := by
        intro i
        letI : IsMarkovKernel
            (pilotProtocol p ε m (select) n i) :=
          (pilotProtocol_private p ε m select hselect hp hε n).1 i
        dsimp [finiteSequenceKernel]
        infer_instance
      let up : Fin r → Fin 4 := fun j => u j.castSucc
      let uf : History (pilotOutputFamily n) (r + 1) hℓn :=
        fun j => (Sum.inl (u j) : PilotOutput)
      let ufp : History (pilotOutputFamily n) r (Nat.le_of_succ_le hℓn) :=
        Fin.init uf
      have hu : uf =
          snoc (Z := pilotOutputFamily n) hℓn
            ufp
            (Sum.inl (u (Fin.last r))) := by
        exact (Fin.snoc_init_self uf).symm
      change (prefixLaw _ x (r + 1) hℓn) {uf} = _
      rw [hu, prefixLaw_succ_singleton _ hQ]
      change (prefixLaw _ x r (Nat.le_of_succ_le hℓn))
          ({((fun j => (Sum.inl (up j) : PilotOutput)) :
            History (pilotOutputFamily n) r (Nat.le_of_succ_le hℓn))} :
              Set (History (pilotOutputFamily n) r (Nat.le_of_succ_le hℓn))) * _ = _
      rw [ih (Nat.le_of_succ_le hℓn) hrm up]
      rw [Fin.prod_univ_castSucc]
      congr 1
      have hidx : nextIndex hℓn = Fin.castLE hℓn (Fin.last r) := Fin.ext rfl
      cases hidx
      dsimp [finiteSequenceKernel, pilotProtocol]
      simp only [nextIndex, Fin.castLE, Fin.last, Nat.succ_eq_add_one]
      change (if r < m n then
          ((rrPilotKernel ε) (x ⟨r, by omega⟩)).map Sum.inl
        else _) {Sum.inl (u (Fin.last r))} = _
      rw [if_pos (by exact_mod_cast (Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hℓm))]
      rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
      have hpre : (Sum.inl : Fin 4 → PilotOutput) ⁻¹'
          ({Sum.inl (u (Fin.last r))} : Set PilotOutput) =
          ({u (Fin.last r)} : Set (Fin 4)) := by ext y; simp
      rw [hpre]
      convert rrPilotKernel_singleton ε (x ⟨r, by omega⟩) (u (Fin.last r))
      rfl

/-- After marginalizing the IID private-input path, every all-pilot prefix atom has the product of the calibrated RR marginal probabilities. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hmn), [the pilot Prefix marginal singleton](goal).

Under the stated assumptions, the pilot Prefix marginal singleton. -/
lemma pilotPrefix_marginal_singleton (θ : TrialParameter) (p ε : ℝ)
    (m : ℕ → ℕ) (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (hε : 0 < ε) {n : ℕ} (hmn : m n ≤ n) (u : Fin (m n) → Fin 4) :
    Measure.map (transcriptPrefix (Z := pilotOutputFamily n) hmn)
        (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n)
        {fun j => (Sum.inl (u j) : PilotOutput)} =
      ∏ j : Fin (m n), ENNReal.ofReal
        (∑ a : Fin 4, piTheta θ p a * rrPilotProbability ε a (u j)) := by
  have hs : MeasurableSet
      ({fun j => (Sum.inl (u j) : PilotOutput)} :
        Set (History (pilotOutputFamily n) (m n) hmn)) := by
    change MeasurableSet ({fun j : Fin (m n) =>
      (Sum.inl (u j) : PilotOutput)} : Set (Fin (m n) → PilotOutput))
    have h := MeasurableSet.univ_pi (fun j =>
      measurableSet_singleton (Sum.inl (u j) : PilotOutput))
    exact (Set.univ_pi_singleton _).symm ▸ h
  rw [Measure.map_apply (measurable_transcriptPrefix hmn)
    hs]
  unfold transcriptLaw
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul]
  have hpath (x : Fin n → Fin 4) : 0 ≤ inputPathProbability θ p x := by
    unfold inputPathProbability
    exact Finset.prod_nonneg fun i _ =>
      (piTheta_pos_interior θ p hp hθ (x i)).le
  have hrr (a k : Fin 4) : 0 ≤ rrPilotProbability ε a k := by
    unfold rrPilotProbability
    split_ifs <;> positivity
  calc
    (∑ x : Fin n → Fin 4,
        ENNReal.ofReal (inputPathProbability θ p x) *
          (pilotEstimator p ε m select hselect hp hε).transcript n x
            (transcriptPrefix hmn ⁻¹' {fun j => Sum.inl (u j)})) =
      ∑ x : Fin n → Fin 4,
        ENNReal.ofReal (inputPathProbability θ p x) *
          ∏ j : Fin (m n), ENNReal.ofReal
            (rrPilotProbability ε (x (Fin.castLE hmn j)) (u j)) := by
        apply Finset.sum_congr rfl
        intro x _
        congr 1
        rw [show (pilotEstimator p ε m select hselect hp hε).transcript n x =
            finiteSequenceTranscript
              (pilotProtocol p ε m (select) n) x by rfl]
        rw [← Measure.map_apply (measurable_transcriptPrefix hmn)
          hs,
          finiteSequenceTranscript_map_prefix _
            (pilotProtocol_private p ε m select hselect hp hε n).1 x hmn]
        exact pilotPrefix_component_singleton select p ε m hselect hp hε hmn le_rfl x u
    _ = ENNReal.ofReal (∑ x : Fin n → Fin 4,
        inputPathProbability θ p x *
          ∏ j : Fin (m n),
            rrPilotProbability ε (x (Fin.castLE hmn j)) (u j)) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        · apply Finset.sum_congr rfl
          intro x _
          rw [ENNReal.ofReal_mul (hpath x), ENNReal.ofReal_prod_of_nonneg]
          intro j _
          exact hrr _ _
        · intro x _
          exact mul_nonneg (hpath x) (Finset.prod_nonneg fun j _ => hrr _ _)
    _ = ENNReal.ofReal (∏ j : Fin (m n),
        ∑ a : Fin 4, piTheta θ p a * rrPilotProbability ε a (u j)) := by
          rw [inputPath_prefix_rr_sum θ p ε hmn u]
    _ = _ := by
      rw [ENNReal.ofReal_prod_of_nonneg]
      intro j _
      exact Finset.sum_nonneg fun a _ =>
        mul_nonneg (piTheta_pos_interior θ p hp hθ a).le (hrr _ _)

/-- For [the supplied quantities and conditions](hyp:u), the [pilot prefix embed](goal) is the mathematical object specified below. -/
def pilotPrefixEmbed {ℓ : ℕ} (u : Fin ℓ → Fin 4) : Fin ℓ → PilotOutput :=
  fun j => Sum.inl (u j)

-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
/-- [the pilot prefix embed injective assertion](goal) holds. -/
lemma pilotPrefixEmbed_injective {ℓ : ℕ} :
    Function.Injective (@pilotPrefixEmbed ℓ) := by
  intro u v huv
  funext j
  exact Sum.inl_injective (congrFun huv j)

/-- The marginalized pilot prefix is concentrated on four-category releases; the masses of those atoms sum to one. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hmn), [the pilot Prefix range measure](goal).

Under the stated assumptions, the pilot Prefix range measure. -/
lemma pilotPrefix_range_measure (θ : TrialParameter) (p ε : ℝ)
    (m : ℕ → ℕ) (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (hε : 0 < ε) {n : ℕ} (hmn : m n ≤ n) :
    Measure.map (transcriptPrefix (Z := pilotOutputFamily n) hmn)
        (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n)
        (Set.range (fun u : Fin (m n) → Fin 4 =>
          ((fun j => Sum.inl (u j)) :
            History (pilotOutputFamily n) (m n) hmn))) = 1 := by
  classical
  let μ := Measure.map (transcriptPrefix (Z := pilotOutputFamily n) hmn)
    (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n)
  let e : (Fin (m n) → Fin 4) →
      History (pilotOutputFamily n) (m n) hmn :=
    fun u j => Sum.inl (u j)
  have he : Function.Injective e := by
    intro u v huv
    funext j
    exact Sum.inl_injective (congrFun huv j)
  letI : MeasurableSingletonClass
      (History (pilotOutputFamily n) (m n) hmn) := by
    constructor
    intro v
    change MeasurableSet ({v} : Set (Fin (m n) → PilotOutput))
    have hv := MeasurableSet.univ_pi (fun j => measurableSet_singleton (v j))
    exact (Set.univ_pi_singleton v).symm ▸ hv
  have hrange : Set.range e =
      (↑(Finset.univ.image e) :
        Set (History (pilotOutputFamily n) (m n) hmn)) := by
    ext z
    simp
  change μ (Set.range e) = 1
  rw [hrange, ← MeasureTheory.sum_measure_singleton]
  rw [Finset.sum_image]
  · rw [show (∑ u ∈ (Finset.univ : Finset (Fin (m n) → Fin 4)), μ {e u}) =
        ∑ u : Fin (m n) → Fin 4,
          ∏ j : Fin (m n), ENNReal.ofReal
            (∑ a : Fin 4, piTheta θ p a * rrPilotProbability ε a (u j)) by
      apply Finset.sum_congr rfl
      intro u _
      change Measure.map (transcriptPrefix (Z := pilotOutputFamily n) hmn)
          (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n)
          {((fun j => Sum.inl (u j)) :
            History (pilotOutputFamily n) (m n) hmn)} = _
      exact pilotPrefix_marginal_singleton select θ p ε m hselect hp hθ hε hmn u]
    calc
      (∑ u : Fin (m n) → Fin 4,
          ∏ j : Fin (m n), ENNReal.ofReal
            (∑ a : Fin 4,
              piTheta θ p a * rrPilotProbability ε a (u j))) =
          ∏ j : Fin (m n), ∑ k : Fin 4, ENNReal.ofReal
            (∑ a : Fin 4,
              piTheta θ p a * rrPilotProbability ε a k) :=
        (Fintype.prod_sum (fun _j : Fin (m n) => fun k : Fin 4 =>
          ENNReal.ofReal (∑ a : Fin 4,
            piTheta θ p a * rrPilotProbability ε a k))).symm
      _ = 1 := by
        apply Finset.prod_eq_one
        intro j _
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · rw [rrPilot_marginal_sum_eq_one]
          simp
        · intro k _
          exact Finset.sum_nonneg fun a _ => mul_nonneg
            (piTheta_pos_interior θ p hp hθ a).le (by
              unfold rrPilotProbability
              split_ifs <;> positivity)
  · exact Set.injOn_of_injective he

/-- The finite pilot prefix has exactly the IID product law of the calibrated four-category randomized-response marginal, embedded into pilot outputs. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hmn), [the pilot Prefix law eq map pi](goal).

Under the stated assumptions, the pilot Prefix law eq map pi. -/
lemma pilotPrefix_law_eq_map_pi (θ : TrialParameter) (p ε : ℝ)
    (m : ℕ → ℕ) (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (hε : 0 < ε) {n : ℕ} (hmn : m n ≤ n) :
    Measure.map (transcriptPrefix (Z := pilotOutputFamily n) hmn)
        (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n) =
      Measure.map
        (fun u : Fin (m n) → Fin 4 =>
          ((fun j => Sum.inl (u j)) :
            History (pilotOutputFamily n) (m n) hmn))
        (Measure.pi fun _ : Fin (m n) => rrPilotMarginal θ p ε) := by
  classical
  let e : (Fin (m n) → Fin 4) →
      History (pilotOutputFamily n) (m n) hmn :=
    fun u j => Sum.inl (u j)
  have he : Function.Injective e := by
    intro u v huv
    funext j
    exact Sum.inl_injective (congrFun huv j)
  have hme : Measurable e := by fun_prop
  letI : IsProbabilityMeasure (rrPilotMarginal θ p ε) :=
    rrPilotMarginal_isProbability θ p ε hp hθ
  letI : IsProbabilityMeasure
      (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n) :=
    transcriptLaw_isProbability _ θ p hp hθ n
  let μ := Measure.map (transcriptPrefix (Z := pilotOutputFamily n) hmn)
    (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n)
  letI : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map (measurable_transcriptPrefix hmn).aemeasurable
  letI : Countable (History (pilotOutputFamily n) (m n) hmn) :=
    inferInstanceAs (Countable (Fin (m n) → PilotOutput))
  letI : MeasurableSingletonClass
      (History (pilotOutputFamily n) (m n) hmn) := by
    constructor
    intro v
    change MeasurableSet ({v} : Set (Fin (m n) → PilotOutput))
    have hv := MeasurableSet.univ_pi (fun j => measurableSet_singleton (v j))
    exact (Set.univ_pi_singleton v).symm ▸ hv
  have hrangeMeas : MeasurableSet (Set.range e) := by
    exact Set.Finite.measurableSet (Set.toFinite (Set.range e))
  have hrange : μ (Set.range e) = 1 := by
    exact pilotPrefix_range_measure select θ p ε m hselect hp hθ hε hmn
  have hcompl : μ (Set.range e)ᶜ = 0 := by
    rw [MeasureTheory.measure_compl hrangeMeas (by simp [hrange]),
      measure_univ, hrange]
    simp
  apply Measure.ext_of_singleton
  intro z
  by_cases hz : z ∈ Set.range e
  · obtain ⟨u, rfl⟩ := hz
    change μ {e u} = (Measure.map e (Measure.pi fun _ : Fin (m n) =>
      rrPilotMarginal θ p ε)) {e u}
    rw [Measure.map_apply hme (measurableSet_singleton _)]
    have hpre : e ⁻¹' ({e u} : Set (History
        (pilotOutputFamily n) (m n) hmn)) = {u} := by
      ext v
      simp [he.eq_iff]
    rw [hpre, Measure.pi_singleton]
    change Measure.map (transcriptPrefix (Z := pilotOutputFamily n) hmn)
        (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n)
        {((fun j => Sum.inl (u j)) :
          History (pilotOutputFamily n) (m n) hmn)} = _
    rw [pilotPrefix_marginal_singleton select θ p ε m hselect hp hθ hε hmn]
    apply Finset.prod_congr rfl
    intro j _
    exact (rrPilotMarginal_singleton θ p ε (u j)).symm
  · change μ {z} = (Measure.map e (Measure.pi fun _ : Fin (m n) =>
      rrPilotMarginal θ p ε)) {z}
    have hzsub : ({z} : Set (History
        (pilotOutputFamily n) (m n) hmn)) ⊆ (Set.range e)ᶜ := by
      intro y hy
      have hyz : y = z := Set.mem_singleton_iff.mp hy
      subst y
      exact hz
    rw [MeasureTheory.measure_mono_null hzsub hcompl]
    rw [Measure.map_apply hme (measurableSet_singleton _)]
    have hpre : e ⁻¹' ({z} : Set (History
        (pilotOutputFamily n) (m n) hmn)) = ∅ := by
      ext u
      change (e u = z) ↔ False
      constructor
      · intro heu
        exact hz ⟨u, heu⟩
      · intro hf
        exact hf.elim
    rw [hpre]
    simp

/-- For [the supplied quantities and conditions](hyp:u,k), the [pilot prefix frequency](goal) is the mathematical object specified below. -/
def pilotPrefixFrequency {ℓ : ℕ} (u : Fin ℓ → Fin 4) (k : Fin 4) : ℝ :=
  (ℓ : ℝ)⁻¹ * ∑ j : Fin ℓ, if u j = k then (1 : ℝ) else 0

/-- For [the supplied quantities and conditions](hyp:v), the [pilot prefix output frequency](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:k), these specify the stated inputs. -/
def pilotPrefixOutputFrequency {ℓ : ℕ} (v : Fin ℓ → PilotOutput)
    (k : Fin 4) : ℝ :=
  (ℓ : ℝ)⁻¹ * ∑ j : Fin ℓ, if v j = Sum.inl k then (1 : ℝ) else 0

/-- Under [the supplied quantities and conditions](hyp:m), [the pilot frequency eq prefix frequency assertion](goal) holds. For [the displayed quantities and conditions](hyp:hmn,z,k), these specify the stated inputs. -/
lemma pilotFrequency_eq_prefixFrequency (m : ℕ → ℕ) {n : ℕ}
    (hmn : m n ≤ n) (z : Transcript (pilotOutputFamily n)) (k : Fin 4) :
    pilotFrequency m z k =
      pilotPrefixOutputFrequency (transcriptPrefix hmn z) k := by
  unfold pilotFrequency pilotPrefixOutputFrequency transcriptPrefix
  congr 1
  calc
    (∑ i : Fin n,
        if i.val < m n ∧ z i = Sum.inl k then (1 : ℝ) else 0) =
        ∑ j : Fin (m n),
          if z (Fin.castLE hmn j) = Sum.inl k then (1 : ℝ) else 0 := by
      rw [← fin_sum_ite_lt hmn (fun j : Fin (m n) =>
        if z (Fin.castLE hmn j) = Sum.inl k then (1 : ℝ) else 0)]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i.val < m n <;> simp [hi]
    _ = _ := rfl

/-- [Each empirical pilot-cell frequency is measurable](goal). -/
@[fun_prop] lemma measurable_pilotFrequency (m : ℕ → ℕ) {n : ℕ} (k : Fin 4) :
    Measurable (fun z : Transcript (pilotOutputFamily n) => pilotFrequency m z k) := by
  unfold pilotFrequency
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  have hi : MeasurableSet {z : Transcript (pilotOutputFamily n) |
      i.val < m n ∧ z i = Sum.inl k} := by
    by_cases hlt : i.val < m n
    · have heval : Measurable (fun z : Transcript (pilotOutputFamily n) => z i) :=
        measurable_pi_apply i
      have heq : {z : Transcript (pilotOutputFamily n) |
          i.val < m n ∧ z i = Sum.inl k} =
          (fun z : Transcript (pilotOutputFamily n) => z i) ⁻¹'
            ({Sum.inl k} : Set PilotOutput) := by
        ext z
        simp [hlt]
      rw [heq]
      exact heval (measurableSet_singleton (Sum.inl k))
    · simp [hlt]
  exact measurable_const.ite hi measurable_const

/-- Under [the supplied quantities and conditions](hyp:u,k), [the pilot prefix frequency embed assertion](goal) holds. -/
lemma pilotPrefixFrequency_embed {ℓ : ℕ} (u : Fin ℓ → Fin 4) (k : Fin 4) :
    pilotPrefixOutputFrequency (fun j => (Sum.inl (u j) : PilotOutput)) k =
      pilotPrefixFrequency u k := by
  unfold pilotPrefixOutputFrequency pilotPrefixFrequency
  simp

/-- Under the supplied quantities and conditions, the pilot frequency map eq pi assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hmn), [the pilot Frequency map eq pi](goal).

Under the stated assumptions, the pilot Frequency map eq pi. -/
lemma pilotFrequency_map_eq_pi (θ : TrialParameter) (p ε : ℝ)
    (m : ℕ → ℕ) (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (hε : 0 < ε) {n : ℕ} (hmn : m n ≤ n) (k : Fin 4) :
    Measure.map (fun z => pilotFrequency m z k)
        (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n) =
      Measure.map (fun u : Fin (m n) → Fin 4 => pilotPrefixFrequency u k)
        (Measure.pi fun _ : Fin (m n) => rrPilotMarginal θ p ε) := by
  let prefixFreq : History (pilotOutputFamily n) (m n) hmn → ℝ :=
    fun v => pilotPrefixOutputFrequency v k
  have hprefixFreq : Measurable prefixFreq := by
    unfold prefixFreq pilotPrefixOutputFrequency
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro j _
    have hj : Measurable (fun v : History
        (pilotOutputFamily n) (m n) hmn => v j) := measurable_pi_apply j
    have hs : MeasurableSet {v : History
        (pilotOutputFamily n) (m n) hmn | v j = Sum.inl k} :=
      hj (measurableSet_singleton (Sum.inl k))
    exact measurable_const.ite hs measurable_const
  have hcomp : (fun z : Transcript (pilotOutputFamily n) =>
      pilotFrequency m z k) =
      prefixFreq ∘ transcriptPrefix hmn := by
    funext z
    exact pilotFrequency_eq_prefixFrequency m hmn z k
  rw [hcomp, ← Measure.map_map hprefixFreq (measurable_transcriptPrefix hmn),
    pilotPrefix_law_eq_map_pi select θ p ε m hselect hp hθ hε hmn]
  let e : (Fin (m n) → Fin 4) →
      History (pilotOutputFamily n) (m n) hmn :=
    fun u j => Sum.inl (u j)
  have hme : Measurable e := by fun_prop
  change Measure.map prefixFreq
      (Measure.map e (Measure.pi fun _ : Fin (m n) => rrPilotMarginal θ p ε)) = _
  rw [Measure.map_map hprefixFreq hme]
  congr 1
  funext u
  exact pilotPrefixFrequency_embed u k

/-- For [the supplied quantities and conditions](hyp:k,a), the [pilot cell indicator](goal) is the mathematical object specified below. -/
def pilotCellIndicator (k a : Fin 4) : ℝ :=
  if a = k then 1 else 0

/-- [Each pilot-cell indicator is measurable](goal). -/
@[fun_prop] lemma measurable_pilotCellIndicator (k : Fin 4) :
    Measurable (pilotCellIndicator k) := by
  unfold pilotCellIndicator
  exact measurable_const.ite (measurableSet_singleton k) measurable_const

/-- Under the supplied quantities and conditions, the integrable pilot cell indicator assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the integrable pilot Cell Indicator](goal).

Under the stated assumptions, the integrable pilot Cell Indicator. -/
lemma integrable_pilotCellIndicator (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (k : Fin 4) :
    Integrable (pilotCellIndicator k) (rrPilotMarginal θ p ε) := by
  letI : IsProbabilityMeasure (rrPilotMarginal θ p ε) :=
    rrPilotMarginal_isProbability θ p ε hp hθ
  exact Integrable.of_bound (measurable_pilotCellIndicator k).aestronglyMeasurable
    1 (ae_of_all _ fun a => by
      unfold pilotCellIndicator
      split_ifs <;> norm_num)

/-- Under the supplied quantities and conditions, the integral pilot cell indicator assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the integral pilot Cell Indicator](goal).

Under the stated assumptions, the integral pilot Cell Indicator. -/
lemma integral_pilotCellIndicator (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (k : Fin 4) :
    ∫ a, pilotCellIndicator k a ∂rrPilotMarginal θ p ε =
      ∑ b : Fin 4, piTheta θ p b * rrPilotProbability ε b k := by
  letI : IsProbabilityMeasure (rrPilotMarginal θ p ε) :=
    rrPilotMarginal_isProbability θ p ε hp hθ
  rw [show pilotCellIndicator k =
      ({k} : Set (Fin 4)).indicator (fun _ => (1 : ℝ)) by
    funext a
    by_cases ha : a = k <;> simp [pilotCellIndicator, ha]]
  rw [integral_indicator (measurableSet_singleton k), integral_const]
  rw [MeasureTheory.measureReal_def, Measure.restrict_apply_univ,
    rrPilotMarginal_singleton]
  simp only [smul_eq_mul, mul_one]
  rw [ENNReal.toReal_ofReal]
  exact Finset.sum_nonneg fun b _ => mul_nonneg
    (piTheta_pos_interior θ p hp hθ b).le (by
      unfold rrPilotProbability
      split_ifs <;> positivity)

/-- Under the supplied quantities and conditions, the pilot prefix frequency map pi eq sample mean assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the pilot Prefix Frequency map pi eq sample Mean](goal).

Under the stated assumptions, the pilot Prefix Frequency map pi eq sample Mean. -/
lemma pilotPrefixFrequency_map_pi_eq_sampleMean (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (N : ℕ) (k : Fin 4) :
    let P := rrPilotMarginal θ p ε
    Measure.map (fun u : Fin N → Fin 4 => pilotPrefixFrequency u k)
        (Measure.pi fun _ : Fin N => P) =
      Measure.map (fun ω : ℕ → Fin 4 =>
          (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, pilotCellIndicator k (ω i))
        (Measure.infinitePi fun _ : ℕ => P) := by
  dsimp
  let P := rrPilotMarginal θ p ε
  letI : IsProbabilityMeasure P := rrPilotMarginal_isProbability θ p ε hp hθ
  let S := Causalean.Stat.iidSample_infinitePi P
  have hpush := Causalean.Stat.iidSample_finN_pushforward S N
  rw [← hpush]
  have hmeanMeas : Measurable (fun u : Fin N → Fin 4 =>
      pilotPrefixFrequency u k) := by
    unfold pilotPrefixFrequency
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro j _
    have hj : Measurable (fun u : Fin N → Fin 4 => u j) := measurable_pi_apply j
    exact measurable_const.ite (hj (measurableSet_singleton k)) measurable_const
  rw [Measure.map_map hmeanMeas (Causalean.Stat.iidSample_finN_measurable S N)]
  congr 1
  funext ω
  change pilotPrefixFrequency (fun j : Fin N => ω j) k = _
  unfold pilotPrefixFrequency pilotCellIndicator
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => if ω i = k then (1 : ℝ) else 0) N

/-- Each released pilot-cell frequency obeys the categorical weak law under the actual finite transcript experiment. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hdiverges,hsublinear), [the pilot Frequency tendsto In Probability](goal).

Under the stated assumptions, the pilot Frequency tendsto In Probability. -/
-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
lemma pilotFrequency_tendstoInProbability (θ : TrialParameter) (p ε : ℝ)
    (m : ℕ → ℕ) (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (hε : 0 < ε) (hdiverges : PilotDiverges m)
    (hsublinear : PilotSublinear m) (k : Fin 4) :
    Causalean.Stat.Modes.TendstoInProbability
      (fun n => transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n)
      (fun n z => pilotFrequency m z k) Filter.atTop
      (fun _ _ => ∑ b : Fin 4,
        piTheta θ p b * rrPilotProbability ε b k) := by
  let P := rrPilotMarginal θ p ε
  letI : IsProbabilityMeasure P := rrPilotMarginal_isProbability θ p ε hp hθ
  let S := Causalean.Stat.iidSample_infinitePi P
  have hw := S.sampleMean_tendsto_inProb
    (measurable_pilotCellIndicator k)
    (integrable_pilotCellIndicator θ p ε hp hθ k)
  rw [integral_pilotCellIndicator θ p ε hp hθ k] at hw
  intro δ hδ
  have hwδ := hw δ hδ
  have hwcomp := hwδ.comp hdiverges
  have hwcomp' : Filter.Tendsto (fun n => (Measure.infinitePi fun _ : ℕ => P)
      {ω | δ ≤ edist (S.sampleMean (pilotCellIndicator k) (m n) ω)
        (∑ b : Fin 4, piTheta θ p b * rrPilotProbability ε b k)})
      Filter.atTop (nhds 0) := by
    convert hwcomp using 1 <;> rfl
  have heq : (fun n => (Measure.infinitePi fun _ : ℕ => P)
        {ω | δ ≤ edist (S.sampleMean (pilotCellIndicator k) (m n) ω)
          (∑ b : Fin 4, piTheta θ p b * rrPilotProbability ε b k)}) =ᶠ[Filter.atTop]
      (fun n => (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n)
        {z | δ ≤ edist (pilotFrequency m z k)
          (∑ b : Fin 4, piTheta θ p b * rrPilotProbability ε b k)}) := by
    change ∀ᶠ n in Filter.atTop,
      (Measure.infinitePi fun _ : ℕ => P)
          {ω | δ ≤ edist (S.sampleMean (pilotCellIndicator k) (m n) ω)
            (∑ b : Fin 4, piTheta θ p b * rrPilotProbability ε b k)} =
        (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n)
          {z | δ ≤ edist (pilotFrequency m z k)
            (∑ b : Fin 4, piTheta θ p b * rrPilotProbability ε b k)}
    apply (Filter.eventually_atTop (α := ℕ)).2
    refine ⟨2, ?_⟩
    intro n hn
    have hmn : m n ≤ n := (hsublinear.2 n hn).2.le
    let B : Set ℝ := {r | δ ≤ edist r
      (∑ b : Fin 4, piTheta θ p b * rrPilotProbability ε b k)}
    have hB : MeasurableSet B := by
      exact measurableSet_le measurable_const (measurable_id.edist measurable_const)
    have hfreq := measurable_pilotFrequency m (n := n) k
    have hsample := S.measurable_sampleMean (measurable_pilotCellIndicator k) (m n)
    have hlaw : Measure.map (fun z => pilotFrequency m z k)
          (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n) =
        Measure.map (S.sampleMean (pilotCellIndicator k) (m n))
          (Measure.infinitePi fun _ : ℕ => P) := by
      calc
        Measure.map (fun z => pilotFrequency m z k)
            (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n) =
            Measure.map (fun u : Fin (m n) → Fin 4 => pilotPrefixFrequency u k)
              (Measure.pi fun _ : Fin (m n) => P) :=
          pilotFrequency_map_eq_pi select θ p ε m hselect hp hθ hε hmn k
        _ = Measure.map (S.sampleMean (pilotCellIndicator k) (m n))
            (Measure.infinitePi fun _ : ℕ => P) := by
          have hbase := pilotPrefixFrequency_map_pi_eq_sampleMean
            θ p ε hp hθ (m n) k
          have hfun : S.sampleMean (pilotCellIndicator k) (m n) =
              fun ω : ℕ → Fin 4 => (m n : ℝ)⁻¹ *
                ∑ i ∈ Finset.range (m n), pilotCellIndicator k (ω i) := by
            funext ω
            rfl
          rw [hfun]
          simpa [P] using hbase
    change (Measure.infinitePi fun _ : ℕ => P)
        ((S.sampleMean (pilotCellIndicator k) (m n)) ⁻¹' B) =
      (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n)
        ((fun z => pilotFrequency m z k) ⁻¹' B)
    rw [← Measure.map_apply hsample hB, ← hlaw, Measure.map_apply hfreq hB]
  exact Filter.Tendsto.congr' heq hwcomp'

end CausalSmith.Stat.LdpAteEfficiencySurface
