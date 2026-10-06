module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CovarianceAssembly
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.RoleMeans
public import Causalean.Mathlib.Probability.IidMeanVariance

/-! Variance transport from the twelve evaluation blocks to canonical independent roles.
These identities connect the exact overlap calculation to the actual sampled procedure;
the first-order coefficient average has precisely the single-record variance divided by m. -/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Any injective selection of evaluation blocks has the canonical product law. -/
-- @node: eval_roles_measurePreserving
lemma eval_roles_measurePreserving (P : ObsLaw) (m d : ℕ) (r : Fin d → Fin 12)
    (hr : Function.Injective r) :
    MeasurePreserving (fun eval : EvalData m => fun i => eval (r i)) (evalLaw P m)
      (Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin m => P.law))) := by
  let μ := Measure.pi (fun _ : Fin m => P.law)
  have hind : iIndepFun (fun i : Fin 12 => fun eval : EvalData m => eval i)
      (evalLaw P m) := iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  refine ⟨by fun_prop, ?_⟩
  rw [(hind.precomp hr).map_fun_eq_pi_map
    (fun _ => (by fun_prop : Measurable _).aemeasurable)]
  congr 1
  funext i
  exact (measurePreserving_eval (fun _ : Fin 12 => μ) (r i)).map_eq

/-- A measurable cross-role kernel has the same variance under selected and canonical roles. -/
-- @node: variance_eval_roleAverage
lemma variance_eval_roleAverage (P : ObsLaw) (m d : ℕ) (r : Fin d → Fin 12)
    (hr : Function.Injective r) (h : (Fin d → Omega) → ℝ) (hh : Measurable h) :
    variance (fun eval : EvalData m => roleAverage d m h (fun i => eval (r i)))
      (evalLaw P m) =
    variance (roleAverage d m h)
      (Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin m => P.law))) := by
  apply (eval_roles_measurePreserving P m d r hr).variance_fun_comp
  have hm : Measurable (roleAverage d m h) := by
    unfold roleAverage
    fun_prop
  exact hm.aemeasurable

/-- Every histogram residual test is square integrable, for all trained realizations. -/
-- @node: memLp_inner_Vres
lemma memLp_inner_Vres (P : ObsLaw) {m : ℕ} (train : Fin m → Omega)
    (mx my J : ℕ) (a : Bool) (f : Hj J) :
    MemLp (fun o => inner ℝ (Vres train mx my J a o) f) 2 P.law := by
  let : MeasurableSpace (Hj J) := borel _
  let : BorelSpace (Hj J) := ⟨rfl⟩
  have hm : Measurable (fun o => inner ℝ (Vres train mx my J a o) f) := by fun_prop
  have hf := chain_finite_range_comp (finite_range_Vres train mx my J a)
    (fun v => inner ℝ v f)
  obtain ⟨C, hC⟩ := hf.isBounded.exists_norm_le
  exact MemLp.of_bound hm.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun o => hC _ ⟨o, rfl⟩))

/-- The first-order sampled coefficient has exactly m-inverse times residual variance.
This uses the original observed law and requires no good-pilot event. -/
-- @node: variance_inner_Uone
lemma variance_inner_Uone (P : ObsLaw) {m : ℕ} (train : Fin m → Omega)
    (mx my J : ℕ) (b : Fin 2) (a : Bool) (f : Hj J) :
    variance (fun eval => inner ℝ (Uone train mx my J eval b a) f) (evalLaw P m) =
      (m : ℝ)⁻¹ * variance (fun o => inner ℝ (Vres train mx my J a o) f) P.law := by
  have hp : MeasurePreserving (fun eval : EvalData m => eval (chainRole b 0))
      (evalLaw P m) (Measure.pi (fun _ : Fin m => P.law)) :=
    measurePreserving_eval
      (fun _ : Fin 12 => Measure.pi (fun _ : Fin m => P.law)) (chainRole b 0)
  have hm : Measurable (fun sample : Fin m → Omega =>
      (m : ℝ)⁻¹ * ∑ i, inner ℝ (Vres train mx my J a (sample i)) f) := by
    let : MeasurableSpace (Hj J) := borel _
    let : BorelSpace (Hj J) := ⟨rfl⟩
    fun_prop
  simp only [Uone, real_inner_smul_left, sum_inner]
  have he := hp.variance_fun_comp hm.aemeasurable
  exact he.trans
    (Causalean.Mathlib.Probability.iid_average_variance P.law m
      (fun o => inner ℝ (Vres train mx my J a o) f)
      (memLp_inner_Vres P train mx my J a f))

/-- A two-coordinate sum is exactly the ordered rectangular sum, including empty roles. -/
-- @node: sum_fin_two_coordinates
lemma sum_fin_two_coordinates {α M : Type*} [Fintype α] [AddCommMonoid M]
    (h : α → α → M) :
    (∑ z : Fin 2 → α, h (z 0) (z 1)) = ∑ i : α, ∑ j : α, h i j := by
  classical
  rw [← (piFinTwoEquiv (fun _ : Fin 2 => α)).symm.sum_comp]
  simp [Fintype.sum_prod_type, piFinTwoEquiv]

/-- A three-coordinate sum is exactly the ordered triple sum. -/
-- @node: sum_fin_three_coordinates
lemma sum_fin_three_coordinates {α M : Type*} [Fintype α] [AddCommMonoid M]
    (h : α → α → α → M) :
    (∑ z : Fin 3 → α, h (z 0) (z 1) (z 2)) =
      ∑ i : α, ∑ j : α, ∑ k : α, h i j k := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin 3 => α)).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk,
    Fin.cons_zero, Fin.cons_succ]
  exact Finset.sum_congr rfl (fun i _ => sum_fin_two_coordinates (h i))

/-- The actual multiband statistic is the canonical two-role average of kernel (4). -/
-- @node: inner_Utwo_eq_roleAverage
lemma inner_Utwo_eq_roleAverage {m : ℕ} (train : Fin m → Omega)
    (mx my L T J : ℕ) (kt : ℕ → ℕ) (eval : EvalData m)
    (b : Fin 2) (a : Bool) (f : Hj J) :
    inner ℝ (Utwo train mx my L T J kt eval b a) f =
      roleAverage 2 m (fun o => Rres train mx a (o 0) *
        ∑ t ∈ Finset.range (T + 1), covariateKernel (kt t) (X (o 0)) (X (o 1)) *
          inner ℝ (Vres train mx my J a (o 1)) (Qband L J t f))
        ![eval (chainRole b 1), eval (chainRole b 2)] := by
  classical
  simp only [Utwo, real_inner_smul_left, sum_inner, Qband_inner, roleAverage]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [sum_fin_two_coordinates (fun i j : Fin m =>
    Rres train mx a (eval (chainRole b 1) i) *
      ∑ t ∈ Finset.range (T + 1),
        covariateKernel (kt t) (X (eval (chainRole b 1) i))
          (X (eval (chainRole b 2) j)) *
          inner ℝ (Vres train mx my J a (eval (chainRole b 2) j)) (Qband L J t f))]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- The actual third-order statistic is the canonical three-role average of kernel (9). -/
-- @node: inner_Uthree_eq_roleAverage
lemma inner_Uthree_eq_roleAverage {m : ℕ} (train : Fin m → Omega)
    (mx my J q : ℕ) (eval : EvalData m) (b : Fin 2) (a : Bool) (f : Hj J) :
    inner ℝ (Uthree train mx my J q eval b a) f =
      roleAverage 3 m (fun o =>
        (Rres train mx a (o 0) * covariateKernel q (X (o 0)) (X (o 1)) *
          Rres train mx a (o 1) * covariateKernel q (X (o 1)) (X (o 2))) *
          inner ℝ (Vres train mx my J a (o 2)) f)
        ![eval (chainRole b 3), eval (chainRole b 4), eval (chainRole b 5)] := by
  simp only [Uthree, real_inner_smul_left, sum_inner, roleAverage]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  exact congrArg (fun s : ℝ => (m : ℝ) ^ (-3 : ℤ) * s)
    (sum_fin_three_coordinates (fun i j k : Fin m =>
      (Rres train mx a (eval (chainRole b 3) i) *
        covariateKernel q (X (eval (chainRole b 3) i)) (X (eval (chainRole b 4) j)) *
        Rres train mx a (eval (chainRole b 4) j) *
        covariateKernel q (X (eval (chainRole b 4) j)) (X (eval (chainRole b 5) k))) *
        inner ℝ (Vres train mx my J a (eval (chainRole b 5) k)) f)).symm

/-- Multiband covariance of the sampled procedure equals canonical two-role variance. -/
-- @node: variance_inner_Utwo_eq_roleAverage
lemma variance_inner_Utwo_eq_roleAverage (P : ObsLaw) {m : ℕ}
    (train : Fin m → Omega) (mx my L T J : ℕ) (kt : ℕ → ℕ)
    (b : Fin 2) (a : Bool) (f : Hj J) :
    variance (fun eval => inner ℝ (Utwo train mx my L T J kt eval b a) f) (evalLaw P m) =
      variance (roleAverage 2 m (fun o => Rres train mx a (o 0) *
        ∑ t ∈ Finset.range (T + 1), covariateKernel (kt t) (X (o 0)) (X (o 1)) *
          inner ℝ (Vres train mx my J a (o 1)) (Qband L J t f)))
        (Measure.pi (fun _ : Fin 2 => Measure.pi (fun _ : Fin m => P.law))) := by
  let : MeasurableSpace (Hj J) := borel _
  let : BorelSpace (Hj J) := ⟨rfl⟩
  have hr : Function.Injective (![chainRole b 1, chainRole b 2] : Fin 2 → Fin 12) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> fin_cases b <;>
      simp_all [chainRole, chainOffset, Fin.ofNat]
  simp_rw [inner_Utwo_eq_roleAverage]
  convert variance_eval_roleAverage P m 2 _ hr
    (fun o => Rres train mx a (o 0) *
      ∑ t ∈ Finset.range (T + 1), covariateKernel (kt t) (X (o 0)) (X (o 1)) *
        inner ℝ (Vres train mx my J a (o 1)) (Qband L J t f))
    (by unfold X; fun_prop) using 2
  funext eval
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Third-order covariance of the sampled procedure equals canonical three-role variance. -/
-- @node: variance_inner_Uthree_eq_roleAverage
lemma variance_inner_Uthree_eq_roleAverage (P : ObsLaw) {m : ℕ}
    (train : Fin m → Omega) (mx my J q : ℕ) (b : Fin 2) (a : Bool) (f : Hj J) :
    variance (fun eval => inner ℝ (Uthree train mx my J q eval b a) f) (evalLaw P m) =
      variance (roleAverage 3 m (fun o =>
        (Rres train mx a (o 0) * covariateKernel q (X (o 0)) (X (o 1)) *
          Rres train mx a (o 1) * covariateKernel q (X (o 1)) (X (o 2))) *
          inner ℝ (Vres train mx my J a (o 2)) f))
        (Measure.pi (fun _ : Fin 3 => Measure.pi (fun _ : Fin m => P.law))) := by
  let : MeasurableSpace (Hj J) := borel _
  let : BorelSpace (Hj J) := ⟨rfl⟩
  have hr : Function.Injective
      (![chainRole b 3, chainRole b 4, chainRole b 5] : Fin 3 → Fin 12) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> fin_cases b <;>
      simp_all [chainRole, chainOffset, Fin.ofNat]
  simp_rw [inner_Uthree_eq_roleAverage]
  convert variance_eval_roleAverage P m 3 _ hr
    (fun o => (Rres train mx a (o 0) * covariateKernel q (X (o 0)) (X (o 1)) *
      Rres train mx a (o 1) * covariateKernel q (X (o 1)) (X (o 2))) *
      inner ℝ (Vres train mx my J a (o 2)) f)
    (by unfold X; fun_prop) using 2
  funext eval
  congr 1
  funext i
  fin_cases i <;> rfl

end CausalSmith.Stat.DensityEffectRoughNull
