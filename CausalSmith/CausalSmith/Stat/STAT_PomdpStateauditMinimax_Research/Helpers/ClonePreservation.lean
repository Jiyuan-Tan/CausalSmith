module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.FullHistory

/-! # Preservation of the POMDP class under fixed-permutation state cloning. -/

@[expose] public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory ProbabilityTheory

-- @node: clonePath_obsProj
/-- Refreshing and relabeling the latent clone coordinate leaves the entire
unaudited observation path unchanged. -/
lemma clonePath_obsProj {T n k m : Nat}
    (π : Fin n × Fin m ≃ Fin (n * m))
    (w : FullPath T 1 n k) (coords : Fin (T + 1) → Fin m) :
    obsProj (clonePath π w coords) = obsProj w := by
  funext t
  rfl

-- @node: clonePath_base_coordinates
/-- A fixed clone relabeling leaves the base state, action, and reward path intact. -/
lemma clonePath_base_coordinates {T n k m : Nat}
    (π : Fin n × Fin m ≃ Fin (n * m))
    (w : FullPath T 1 n k) (coords : Fin (T + 1) → Fin m) :
    (∀ t : Fin (T + 1),
      ((stateAt (clonePath π w coords) t).1,
        (π.symm (stateAt (clonePath π w coords) t).2).1) = stateAt w t) ∧
    (∀ t : Fin T, actionAt (clonePath π w coords) t = actionAt w t) ∧
    (∀ t : Fin T, rewardAt (clonePath π w coords) t = rewardAt w t) := by
  constructor
  · intro t
    simp [stateAt, clonePath]
  constructor
  · intro t
    rfl
  · intro t
    rfl

-- @node: clonePath_joint_draw
/-- Decoding the next cloned state recovers the joint reward and next-state draw. -/
lemma clonePath_joint_draw {T n k m : Nat}
    (π : Fin n × Fin m ≃ Fin (n * m))
    (w : FullPath T 1 n k) (coords : Fin (T + 1) → Fin m) (t : Fin T) :
    (rewardAt (clonePath π w coords) t,
      ((nextState (clonePath π w coords) t).1,
        (π.symm (nextState (clonePath π w coords) t).2).1)) =
      (rewardAt w t, nextState w t) := by
  simp [rewardAt, nextState, clonePath]

-- @node: clone_obsLaw
/-- Every fixed clone atom has exactly the same unaudited observation law as
its base model. -/
lemma clone_obsLaw {T n k m : Nat}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m)
    (π : Fin n × Fin m ≃ Fin (n * m)) :
    obsLaw (cloneModel M hm π) = obsLaw M := by
  have hcoord : IsProbabilityMeasure (uniformFin m) := uniformFin_prob m hm
  letI : IsProbabilityMeasure (uniformFin m) := hcoord
  have hobsBase : Measurable (obsProj (T := T) (nX := 1) (nH := n) (k := k)) := by
    unfold obsProj currentState actionAt rewardAt
    fun_prop
  have hobsClone : Measurable (obsProj (T := T) (nX := 1) (nH := n * m) (k := k)) := by
    unfold obsProj currentState actionAt rewardAt
    fun_prop
  have hclone : Measurable (fun q : FullPath T 1 n k × (Fin (T + 1) → Fin m) =>
      clonePath π q.1 q.2) := by
    unfold clonePath
    fun_prop
  unfold obsLaw
  change (clonePathLaw M π).map obsProj = M.law.map obsProj
  unfold clonePathLaw
  rw [Measure.map_map hobsClone hclone]
  have hfun : (fun q : FullPath T 1 n k × (Fin (T + 1) → Fin m) =>
      obsProj (clonePath π q.1 q.2)) = fun q => obsProj q.1 := by
    funext q
    exact clonePath_obsProj π q.1 q.2
  change Measure.map (fun q => obsProj (clonePath π q.1 q.2))
      (M.law.prod (Measure.pi (fun _ : Fin (T + 1) => uniformFin m))) =
    M.law.map obsProj
  rw [hfun]
  calc
    (M.law.prod (Measure.pi (fun _ : Fin (T + 1) => uniformFin m))).map
        (fun q => obsProj q.1) =
      ((M.law.prod (Measure.pi (fun _ : Fin (T + 1) => uniformFin m))).map
        Prod.fst).map obsProj := (Measure.map_map hobsBase measurable_fst).symm
    _ = M.law.map obsProj := by simp

noncomputable def stationaryRatio {T nX nH k : Nat} (M : PomdpModel T nX nH k)
    (s : JointState nX nH) : ℝ :=
  let db := stationaryLaw (policyKernel M M.b) s
  if db = 0 then 0 else stationaryLaw (policyKernel M M.e) s / db

-- @node: clone_policyOverlap
/-- Cloning a constant-observation model leaves its policy overlap unchanged. -/
lemma clone_policyOverlap {T n k m : Nat} {zeta : ℝ}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m)
    (π : Fin n × Fin m ≃ Fin (n * m))
    (hOverlap : PolicyOverlap zeta M) :
    PolicyOverlap zeta (cloneModel M hm π) := by
  exact hOverlap

-- @node: clone_kernel_probability
/-- A cloned reward and next-state kernel is a probability measure. -/
lemma clone_kernel_probability {T n k m : Nat}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m)
    (π : Fin n × Fin m ≃ Fin (n * m))
    (hKernel : FullFiltrationPomdp M)
    (s : JointState 1 (n * m)) (a : Fin k) :
    IsProbabilityMeasure (cloneKernel M π s a) := by
  letI : IsProbabilityMeasure (M.K (s.1, (π.symm s.2).1) a) := hKernel.1 _ _
  have hmap (i : Fin m) :
      (Measure.map (fun q : ℝ × JointState 1 n =>
        (q.1, (q.2.1, π (q.2.2, i))))
        (M.K (s.1, (π.symm s.2).1) a)) Set.univ = 1 := by
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
    simp
  unfold cloneKernel
  constructor
  simp [hmap]
  rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast hm), ENNReal.ofReal_natCast]
  exact ENNReal.mul_inv_cancel (a := (m : ENNReal))
    (by exact_mod_cast (Nat.ne_of_gt hm)) (by simp)

-- @node: clone_kernel_cell_mass
/-- Each next clone coordinate receives one `m`th of its base joint-state mass. -/
lemma clone_kernel_cell_mass {T n k m : Nat}
    (M : PomdpModel T 1 n k) (π : Fin n × Fin m ≃ Fin (n * m))
    (s : JointState 1 (n * m)) (a : Fin k)
    (s' : JointState 1 n) (i' : Fin m) :
    cloneKernel M π s a {q | q.2 = (s'.1, π (s'.2, i'))} =
      ENNReal.ofReal (1 / (m : ℝ)) *
        M.K (s.1, (π.symm s.2).1) a {q | q.2 = s'} := by
  unfold cloneKernel
  rw [Measure.finsetSum_apply]
  simp_rw [Measure.smul_apply, smul_eq_mul]
  have hterm (i : Fin m) :
      (M.K (s.1, (π.symm s.2).1) a).map
        (fun q : ℝ × JointState 1 n => (q.1, (q.2.1, π (q.2.2, i))))
        {q | q.2 = (s'.1, π (s'.2, i'))} =
        if i = i' then M.K (s.1, (π.symm s.2).1) a {q | q.2 = s'} else 0 := by
    rw [Measure.map_apply (by fun_prop) (by measurability)]
    by_cases hi : i = i'
    · subst i
      have hset : (fun q : ℝ × JointState 1 n =>
          (q.1, (q.2.1, π (q.2.2, i')))) ⁻¹'
          {q | q.2 = (s'.1, π (s'.2, i'))} = {q | q.2 = s'} := by
        ext q
        rcases q with ⟨y, ⟨x, h⟩⟩
        rcases s' with ⟨x', h'⟩
        simp [Prod.mk.injEq]
      rw [hset]
      simp
    · have hset : (fun q : ℝ × JointState 1 n =>
          (q.1, (q.2.1, π (q.2.2, i)))) ⁻¹'
          {q | q.2 = (s'.1, π (s'.2, i'))} = ∅ := by
        ext q
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        intro h
        have hpair : (q.2.2, i) = (s'.2, i') := π.injective (congrArg Prod.snd h)
        exact hi (congrArg Prod.snd hpair)
      rw [hset]
      simp [hi]
  simp_rw [hterm]
  simp

-- @node: clone_policyKernel_cell
/-- The cloned state transition to a fixed clone is the decoded base transition
divided by the clone multiplicity. -/
lemma clone_policyKernel_cell {T n k m : Nat}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m)
    (π : Fin n × Fin m ≃ Fin (n * m)) (p : Policy 1 k)
    (s : JointState 1 (n * m)) (s' : JointState 1 n) (i' : Fin m) :
    policyKernel (cloneModel M hm π) p s (s'.1, π (s'.2, i')) =
      policyKernel M p (s.1, (π.symm s.2).1) s' / (m : ℝ) := by
  unfold policyKernel
  change (∑ a : Fin k, p s.1 a *
    (cloneKernel M π s a {q | q.2 = (s'.1, π (s'.2, i'))}).toReal) = _
  simp_rw [clone_kernel_cell_mass, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (1 : ℝ) / (m : ℝ))]
  simp_rw [show ∀ x y : ℝ, x * (1 / (m : ℝ) * y) = (x * y) / (m : ℝ) by
    intro x y
    ring]
  rw [Finset.sum_div]

-- @node: clone_applyKernel_uniformLift
/-- Applying a cloned policy kernel to a uniform lift yields the uniform lift
of the base one-step state law. -/
lemma clone_applyKernel_uniformLift {T n k m : Nat}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m)
    (π : Fin n × Fin m ≃ Fin (n * m)) (p : Policy 1 k)
    (d : JointState 1 n → ℝ) (s' : JointState 1 n) (i' : Fin m) :
    applyKernel
      (fun s : JointState 1 (n * m) => d (s.1, (π.symm s.2).1) / (m : ℝ))
      (policyKernel (cloneModel M hm π) p) (s'.1, π (s'.2, i')) =
      applyKernel d (policyKernel M p) s' / (m : ℝ) := by
  unfold applyKernel
  simp only [Fintype.sum_prod_type, Fin.sum_univ_one]
  rw [← Equiv.sum_comp π]
  simp only [Fintype.sum_prod_type, π.symm_apply_apply]
  simp_rw [clone_policyKernel_cell]
  simp only [π.symm_apply_apply]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro h _
  field_simp

-- @node: clone_uniformLift_stationary
/-- A stationary base probability vector lifts to a stationary cloned vector. -/
lemma clone_uniformLift_stationary {T n k m : Nat}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m)
    (π : Fin n × Fin m ≃ Fin (n * m)) (p : Policy 1 k)
    (d : JointState 1 n → ℝ)
    (hd : IsStationary (policyKernel M p) d) :
    IsStationary (policyKernel (cloneModel M hm π) p)
      (fun s : JointState 1 (n * m) =>
        d (s.1, (π.symm s.2).1) / (m : ℝ)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  constructor
  · constructor
    · intro s
      exact div_nonneg (hd.1.1 _) (le_of_lt hmpos)
    · simp only [Fintype.sum_prod_type, Fin.sum_univ_one]
      rw [← Equiv.sum_comp π]
      simp only [Fintype.sum_prod_type, π.symm_apply_apply]
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      simp_rw [mul_div_cancel₀ _ hm0]
      simpa only [Fintype.sum_prod_type, Fin.sum_univ_one] using hd.1.2
  · intro s
    rcases s with ⟨x, j⟩
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    have h := clone_applyKernel_uniformLift M hm π p d
      (0, (π.symm j).1) (π.symm j).2
    simp only [π.apply_symm_apply] at h
    change applyKernel
      (fun s : JointState 1 (n * m) => d (s.1, (π.symm s.2).1) / (m : ℝ))
      (policyKernel (cloneModel M hm π) p) (0, j) = _
    rw [h]
    have hfix := hd.2 (0, (π.symm j).1)
    change applyKernel d (policyKernel M p) (0, (π.symm j).1) =
      d (0, (π.symm j).1) at hfix
    rw [hfix]

-- @node: clone_kernel_reward_marginal
/-- Clone refresh does not change the conditional reward distribution. -/
lemma clone_kernel_reward_marginal {T n k m : Nat}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m)
    (π : Fin n × Fin m ≃ Fin (n * m))
    (s : JointState 1 (n * m)) (a : Fin k) :
    (cloneKernel M π s a).map Prod.fst =
      (M.K (s.1, (π.symm s.2).1) a).map Prod.fst := by
  unfold cloneKernel
  rw [← Measure.mapₗ_apply_of_measurable measurable_fst, map_sum]
  simp_rw [map_smul, Measure.mapₗ_apply_of_measurable measurable_fst]
  have hmap (i : Fin m) :
      (Measure.map Prod.fst
        (Measure.map (fun q : ℝ × JointState 1 n =>
          (q.1, (q.2.1, π (q.2.2, i))))
          (M.K (s.1, (π.symm s.2).1) a))) =
        (M.K (s.1, (π.symm s.2).1) a).map Prod.fst := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  simp_rw [hmap]
  rw [← Finset.sum_smul]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [one_div]
  rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast hm), ENNReal.ofReal_natCast,
    ENNReal.mul_inv_cancel (by exact_mod_cast (Nat.ne_of_gt hm)) (by simp)]
  exact one_smul _ _

-- @node: clone_kernel_reward_moments
/-- The cloned kernel preserves both reward moments required by the envelope. -/
lemma clone_kernel_reward_moments {T n k m : Nat}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m)
    (π : Fin n × Fin m ≃ Fin (n * m))
    (s : JointState 1 (n * m)) (a : Fin k) :
    (∫ q, q.1 ∂cloneKernel M π s a) =
      ∫ q, q.1 ∂M.K (s.1, (π.symm s.2).1) a ∧
    (∫ q, q.1 ^ 2 ∂cloneKernel M π s a) =
      ∫ q, q.1 ^ 2 ∂M.K (s.1, (π.symm s.2).1) a := by
  have h := clone_kernel_reward_marginal M hm π s a
  constructor
  · have hc := integral_map_of_stronglyMeasurable (μ := cloneKernel M π s a)
        (φ := Prod.fst) (f := id) (by fun_prop) (by fun_prop)
    have hb := integral_map_of_stronglyMeasurable
        (μ := M.K (s.1, (π.symm s.2).1) a)
        (φ := Prod.fst) (f := id) (by fun_prop) (by fun_prop)
    simpa only [id_eq] using hc.symm.trans (h ▸ hb)
  · have hc := integral_map_of_stronglyMeasurable (μ := cloneKernel M π s a)
        (φ := Prod.fst) (f := fun x : ℝ => x ^ 2) (by fun_prop) (by fun_prop)
    have hb := integral_map_of_stronglyMeasurable
        (μ := M.K (s.1, (π.symm s.2).1) a)
        (φ := Prod.fst) (f := fun x : ℝ => x ^ 2) (by fun_prop) (by fun_prop)
    exact hc.symm.trans (h ▸ hb)

-- @node: clone_reward_moment_envelope
/-- The complete first and second reward moment envelope survives cloning. -/
lemma clone_reward_moment_envelope {T n k m : Nat}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m)
    (π : Fin n × Fin m ≃ Fin (n * m))
    (hMoment : RewardMomentEnvelope M) :
    RewardMomentEnvelope (cloneModel M hm π) := by
  intro s a
  have hbase := hMoment (s.1, (π.symm s.2).1) a
  have hmarg := clone_kernel_reward_marginal M hm π s a
  have hmeans := clone_kernel_reward_moments M hm π s a
  have hcomp (f : ℝ → ℝ) (hf : StronglyMeasurable f)
      (hb : Integrable (fun q : ℝ × JointState 1 n => f q.1)
        (M.K (s.1, (π.symm s.2).1) a)) :
      Integrable (fun q : ℝ × JointState 1 (n * m) => f q.1)
        (cloneKernel M π s a) := by
    have hbm : Integrable f ((M.K (s.1, (π.symm s.2).1) a).map Prod.fst) :=
      (integrable_map_measure hf.aestronglyMeasurable measurable_fst.aemeasurable).2 hb
    rw [← hmarg] at hbm
    exact (integrable_map_measure hf.aestronglyMeasurable
      measurable_fst.aemeasurable).1 hbm
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hcomp id (by fun_prop) hbase.1
  · exact hcomp (fun x => x ^ 2) (by fun_prop) hbase.2.1
  · simpa only [cloneModel, hmeans.1] using hbase.2.2.1
  · simpa only [cloneModel, hmeans.2] using hbase.2.2.2

-- @node: clone_rewardRegression
/-- Decoding a cloned state recovers its target-policy reward regression. -/
lemma clone_rewardRegression {T n k m : Nat}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m)
    (π : Fin n × Fin m ≃ Fin (n * m)) (s : JointState 1 (n * m)) :
    rewardRegression (cloneModel M hm π) s =
      rewardRegression M (s.1, (π.symm s.2).1) := by
  simp only [rewardRegression]
  apply Finset.sum_congr rfl
  intro a _
  rw [show (cloneModel M hm π).e = M.e from rfl]
  change M.e s.1 a * ∫ q, q.1 ∂cloneKernel M π s a = _
  rw [(clone_kernel_reward_moments M hm π s a).1]

-- @node: clone_targetValue_of_lift
/-- A uniform lift of the target stationary law preserves the target value. -/
lemma clone_targetValue_of_lift {T n k m : Nat}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m)
    (π : Fin n × Fin m ≃ Fin (n * m))
    (hlift : ∀ h i,
      stationaryLaw (policyKernel (cloneModel M hm π) M.e) (0, π (h, i)) =
        stationaryLaw (policyKernel M M.e) (0, h) / (m : ℝ)) :
    targetValue (cloneModel M hm π) = targetValue M := by
  unfold targetValue
  simp only [Fintype.sum_prod_type, Fin.sum_univ_one]
  rw [← Equiv.sum_comp π]
  simp only [Fintype.sum_prod_type]
  rw [show (cloneModel M hm π).e = M.e from rfl]
  simp_rw [hlift]
  simp_rw [clone_rewardRegression, π.symm_apply_apply]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro h _
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  field_simp

-- @node: clone_stationaryRatio_of_lift
/-- The uniform lift of both stationary laws preserves their pointwise ratio. -/
lemma clone_stationaryRatio_of_lift {T n k m : Nat}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m)
    (π : Fin n × Fin m ≃ Fin (n * m))
    (hlift : ∀ p, (p = M.b ∨ p = M.e) → ∀ h i,
      stationaryLaw (policyKernel (cloneModel M hm π) p) (⟨0, by decide⟩, π (h, i)) =
        stationaryLaw (policyKernel M p) (⟨0, by decide⟩, h) / (m : ℝ)) :
    ∀ h i, stationaryRatio (cloneModel M hm π) (⟨0, by decide⟩, π (h, i)) =
      stationaryRatio M (⟨0, by decide⟩, h) := by
  intro h i
  have hbpol : (cloneModel M hm π).b = M.b := rfl
  have hepol : (cloneModel M hm π).e = M.e := rfl
  rw [stationaryRatio, stationaryRatio, hbpol, hepol,
    hlift M.b (Or.inl rfl) h i,
    hlift M.e (Or.inr rfl) h i]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  by_cases hb : stationaryLaw (policyKernel M M.b) (⟨0, by decide⟩, h) = 0
  · change stationaryLaw (policyKernel M M.b) (0, h) = 0 at hb
    simp [hb]
  · have hb' : stationaryLaw (policyKernel M M.b) (⟨0, by decide⟩, h) /
        (m : ℝ) ≠ 0 := div_ne_zero hb hm0
    simp only [if_neg hb', if_neg hb]
    field_simp

-- @node: stationary_unique_of_uniformContraction
/-- Strict total-variation contraction determines a stationary probability vector
uniquely. This also applies to the cloned policy kernels. -/
lemma stationary_unique_of_uniformContraction {S : Type*} [Fintype S]
    (P : S → S → ℝ) (α : ℝ) (hα : α < 1)
    (hcontract : ∀ p q, ProbabilityVector p → ProbabilityVector q →
      tvNorm (applyKernel p P - applyKernel q P) ≤ α * tvNorm (p - q))
    {p q : S → ℝ} (hp : IsStationary P p) (hq : IsStationary P q) : p = q := by
  have hfixp : applyKernel p P = p := funext hp.2
  have hfixq : applyKernel q P = q := funext hq.2
  have hc := hcontract p q hp.1 hq.1
  rw [hfixp, hfixq] at hc
  have htv_nonneg : 0 ≤ tvNorm (p - q) := by
    unfold tvNorm
    positivity
  have htv_zero : tvNorm (p - q) = 0 := by nlinarith
  have hsum : ∑ s, |p s - q s| = 0 := by
    unfold tvNorm at htv_zero
    norm_num at htv_zero
    simpa [Pi.sub_apply] using htv_zero
  funext s
  have habs : |p s - q s| = 0 := by
    apply le_antisymm
    · calc
        |p s - q s| ≤ ∑ i, |p i - q i| :=
          Finset.single_le_sum (fun i _ => abs_nonneg (p i - q i)) (Finset.mem_univ s)
        _ = 0 := hsum
    · exact abs_nonneg _
  exact sub_eq_zero.mp (abs_eq_zero.mp habs)

-- @node: stationaryLaw_eq_of_uniformContraction
/-- Any explicitly constructed stationary vector is the selected stationary law
under strict contraction. -/
lemma stationaryLaw_eq_of_uniformContraction {S : Type*} [Fintype S]
    (P : S → S → ℝ) (α : ℝ) (hα : α < 1)
    (hcontract : ∀ p q, ProbabilityVector p → ProbabilityVector q →
      tvNorm (applyKernel p P - applyKernel q P) ≤ α * tvNorm (p - q))
    {p : S → ℝ} (hp : IsStationary P p) : stationaryLaw P = p := by
  have hselected : IsStationary P (stationaryLaw P) :=
    Classical.epsilon_spec ⟨p, hp⟩
  exact stationary_unique_of_uniformContraction P α hα hcontract hselected hp

-- @node: clone_stationaryLaw_uniformLift
/-- Once contraction is established, a stationary base vector determines the
selected stationary law of the cloned kernel. -/
lemma clone_stationaryLaw_uniformLift {T n k m : Nat} {t0 : ℝ}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m)
    (π : Fin n × Fin m ≃ Fin (n * m)) (p : Policy 1 k)
    (ht0 : 0 < t0) (hcontract : UniformContraction t0 (cloneModel M hm π))
    (hp : p = M.b ∨ p = M.e)
    (hbase : IsStationary (policyKernel M p) (stationaryLaw (policyKernel M p)))
    (h i) :
    stationaryLaw (policyKernel (cloneModel M hm π) p) (0, π (h, i)) =
      stationaryLaw (policyKernel M p) (0, h) / (m : ℝ) := by
  have hα : mixingAlpha t0 < 1 := by
    rw [mixingAlpha, Real.exp_lt_one_iff]
    exact neg_neg_of_pos (one_div_pos.mpr ht0)
  have h := stationaryLaw_eq_of_uniformContraction
    (policyKernel (cloneModel M hm π) p) (mixingAlpha t0) hα
    (hcontract p hp)
    (clone_uniformLift_stationary M hm π p _ hbase)
  rw [h]
  simp

-- @node: tvNorm_uniformLift
/-- Spreading each base mass uniformly over clone coordinates preserves the
finite total-variation norm. -/
lemma tvNorm_uniformLift {n m : Nat} (hm : 1 ≤ m) (v : Fin n → ℝ) :
    tvNorm (fun q : Fin n × Fin m => v q.1 / (m : ℝ)) = tvNorm v := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  unfold tvNorm
  simp only [Fintype.sum_prod_type]
  simp_rw [abs_div, abs_of_pos hmpos]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hterm (x : ℝ) : (m : ℝ) * (|x| / (m : ℝ)) = |x| := by
    field_simp
  simp_rw [hterm]

-- @node: tvNorm_pushdown_le
/-- Forgetting the clone coordinate cannot increase total variation. -/
lemma tvNorm_pushdown_le {n m : Nat} (v : Fin n × Fin m → ℝ) :
    tvNorm (fun h : Fin n => ∑ i : Fin m, v (h, i)) ≤ tvNorm v := by
  unfold tvNorm
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    ∑ h : Fin n, |∑ i : Fin m, v (h, i)| ≤
        ∑ h : Fin n, ∑ i : Fin m, |v (h, i)| := by
      apply Finset.sum_le_sum
      intro h _
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ q : Fin n × Fin m, |v q| := by
      simp only [Fintype.sum_prod_type]

-- @node: clone_pushdown_probabilityVector
/-- Summing clone masses over their coordinates gives a base probability vector. -/
lemma clone_pushdown_probabilityVector {n m : Nat}
    (d : JointState 1 (n * m) → ℝ) (hd : ProbabilityVector d)
    (π : Fin n × Fin m ≃ Fin (n * m)) :
    ProbabilityVector (fun s : JointState 1 n => ∑ i : Fin m, d (s.1, π (s.2, i))) := by
  constructor
  · intro s
    exact Finset.sum_nonneg (fun i _ => hd.1 _)
  · simp only [Fintype.sum_prod_type, Fin.sum_univ_one]
    have hsum := hd.2
    simp only [Fintype.sum_prod_type, Fin.sum_univ_one] at hsum
    rw [← Equiv.sum_comp π] at hsum
    simpa only [Fintype.sum_prod_type] using hsum

-- @node: clone_applyKernel_pushdown
/-- A cloned transition is the uniform lift of the base transition applied to
the pushed-down input law. -/
lemma clone_applyKernel_pushdown {T n k m : Nat}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m)
    (π : Fin n × Fin m ≃ Fin (n * m)) (p : Policy 1 k)
    (d : JointState 1 (n * m) → ℝ) (s' : JointState 1 n) (i' : Fin m) :
    applyKernel d (policyKernel (cloneModel M hm π) p) (s'.1, π (s'.2, i')) =
      applyKernel (fun s : JointState 1 n => ∑ i : Fin m, d (s.1, π (s.2, i)))
        (policyKernel M p) s' / (m : ℝ) := by
  unfold applyKernel
  simp only [Fintype.sum_prod_type, Fin.sum_univ_one]
  rw [← Equiv.sum_comp π]
  simp only [Fintype.sum_prod_type]
  simp_rw [clone_policyKernel_cell]
  simp only [π.symm_apply_apply]
  simp_rw [show ∀ x y : ℝ, x * (y / (m : ℝ)) = (x * y) / (m : ℝ) by
    intro x y
    ring]
  simp_rw [Finset.sum_div]
  congr 1
  funext h
  rw [Finset.sum_mul, Finset.sum_div]

-- @node: tvNorm_clone_relabel
/-- Relabeling the cloned alphabet does not change its total-variation norm. -/
lemma tvNorm_clone_relabel {n m : Nat}
    (π : Fin n × Fin m ≃ Fin (n * m))
    (v : JointState 1 (n * m) → ℝ) :
    tvNorm v = tvNorm (fun q : Fin n × Fin m => v (0, π q)) := by
  unfold tvNorm
  simp only [Fintype.sum_prod_type, Fin.sum_univ_one]
  rw [← Equiv.sum_comp π]
  simp only [Fintype.sum_prod_type]

-- @node: clone_uniformContraction
/-- The clone transition contracts because pushdown decreases total variation
and uniform lifting preserves it. -/
lemma clone_uniformContraction {T n k m : Nat} {t0 : ℝ}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m)
    (π : Fin n × Fin m ≃ Fin (n * m))
    (hbase : UniformContraction t0 M) :
    UniformContraction t0 (cloneModel M hm π) := by
  intro p hp d d' hd hd'
  let down (v : JointState 1 (n * m) → ℝ) : JointState 1 n → ℝ :=
    fun s => ∑ i : Fin m, v (s.1, π (s.2, i))
  have hdown : ProbabilityVector (down d) :=
    clone_pushdown_probabilityVector d hd π
  have hdown' : ProbabilityVector (down d') :=
    clone_pushdown_probabilityVector d' hd' π
  have hbasebound := hbase p hp (down d) (down d') hdown hdown'
  have hout : tvNorm
      (applyKernel d (policyKernel (cloneModel M hm π) p) -
        applyKernel d' (policyKernel (cloneModel M hm π) p)) =
      tvNorm (applyKernel (down d) (policyKernel M p) -
        applyKernel (down d') (policyKernel M p)) := by
    rw [tvNorm_clone_relabel π]
    convert tvNorm_uniformLift hm
      (fun s : Fin n =>
        applyKernel (down d) (policyKernel M p) (0, s) -
          applyKernel (down d') (policyKernel M p) (0, s)) using 1
    · congr 1
      funext q
      simp only [Pi.sub_apply]
      rw [clone_applyKernel_pushdown M hm π p d (0, q.1) q.2,
        clone_applyKernel_pushdown M hm π p d' (0, q.1) q.2]
      ring
    · unfold tvNorm
      simp only [Fintype.sum_prod_type, Fin.sum_univ_one, Pi.sub_apply]
  have hin : tvNorm (down d - down d') ≤ tvNorm (d - d') := by
    rw [tvNorm_clone_relabel π]
    have hdiff : down d - down d' = fun h : JointState 1 n =>
        ∑ i : Fin m, (d - d') (h.1, π (h.2, i)) := by
      funext s
      simp only [down, Pi.sub_apply, Finset.sum_sub_distrib]
    rw [hdiff]
    convert tvNorm_pushdown_le
      (fun q : Fin n × Fin m => (d - d') (0, π q)) using 1 <;>
      unfold tvNorm <;> simp only [Fintype.sum_prod_type, Fin.sum_univ_one]
  rw [hout]
  exact hbasebound.trans (mul_le_mul_of_nonneg_left hin (by
    unfold mixingAlpha
    positivity))

end CausalSmith.Stat.PomdpStateauditMinimax
