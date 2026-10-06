module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.LocalPolynomial
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.PopulationGram
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.RectangularCoordinates
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.RectangularRoleTransport
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.RectangularVarianceBounds

/-!
# Helpers/RectangularSampling

Two-channel point-CATE annotation frontier: Helpers/RectangularSampling
constructions and obligations.
-/

public section

attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier


-- @node: lem:rectangular-sampling-bound
/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the rectangular sampling bound conclusion](goal) holds. -/
lemma rectangular_sampling_bound (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ C : ℝ, 0 < C ∧ -- @realizes C(finite positive claim-local constant)
       ∀ (P : PrimitiveLaw d), PrimitiveClass alpha beta gamma L eps P →
      ∀ (n m : ℕ) (h : ℝ) (J : ℕ), 2 ≤ n → 0 < h → h ≤ 1/2 → 1 ≤ J →
      (∫ w, ∑ u : PolyIdx d, (rHat w.1 h J u-rBar P n m h J u)^2 ∂experiment P n m) +
      (∫ w, ∑ u : PolyIdx d, ∑ v : PolyIdx d,
        (qHat w.1 h J u v-qPop P n m h J u v)^2 ∂experiment P n m) ≤
      C*(1/((n:ℝ)*h^d)+(Fintype.card (PolyIdx d):ℝ)*(J:ℝ)^d /
        ((n:ℝ)*((n:ℝ)+m)*h^(2*d))) := by
  classical
  let q : ℝ := Fintype.card (PolyIdx d)
  let K := rectangularCoordinateConstant d
  have hK : 0 < K := by dsimp [K, rectangularCoordinateConstant]; positivity
  refine ⟨(q+q*q+1)*K, by dsimp [q]; positivity, ?_⟩
  intro P hP n m h J hn hh hh' hJ
  letI := population_experiment_probability P n m
  let V := 1/((n:ℝ)*h^d)+(Fintype.card (PolyIdx d):ℝ)*(J:ℝ)^d /
    ((n:ℝ)*((n:ℝ)+m)*h^(2*d))
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hr (u : PolyIdx d) := rectangular_r_coordinate_bound (m := m) P hP hn h J hh hh' hJ u
  have hq (u v : PolyIdx d) := rectangular_q_coordinate_bound (m := m) P hP hn h J hh hh' hJ u v
  have hiR (u : PolyIdx d) : Integrable (fun w : Sample d n m =>
      (rHat w.1 h J u-rBar P n m h J u)^2) (experiment P n m) :=
    ((hr u).1.sub (memLp_const _)).integrable_sq
  have hiRaw (u v : PolyIdx d) : Integrable (fun w : Sample d n m =>
      (qRaw w.1 h J u v-∫ z, qRaw z.1 h J u v ∂experiment P n m)^2) (experiment P n m) :=
    ((hq u v).1.sub (memLp_const _)).integrable_sq
  have hmean (u v : PolyIdx d) : qPop P n m h J u v =
      ((∫ w, qRaw w.1 h J u v ∂experiment P n m)+
        (∫ w, qRaw w.1 h J v u ∂experiment P n m))/2 := by
    unfold qPop qHat
    simp_rw [div_eq_mul_inv]
    rw [integral_mul_const, integral_add ((hq u v).1.integrable (by norm_num))
      ((hq v u).1.integrable (by norm_num))]
  have hiQ (u v : PolyIdx d) : Integrable (fun w : Sample d n m =>
      (qHat w.1 h J u v-qPop P n m h J u v)^2) (experiment P n m) := by
    have hm : MemLp (fun w : Sample d n m => qHat w.1 h J u v) 2 (experiment P n m) := by
      simpa only [qHat, div_eq_mul_inv, Pi.add_apply] using ((hq u v).1.add (hq v u).1).mul_const (2:ℝ)⁻¹
    exact (hm.sub (memLp_const _)).integrable_sq
  have hsym (w : Sample d n m) :
      (∑ u : PolyIdx d, ∑ v : PolyIdx d, (qHat w.1 h J u v-qPop P n m h J u v)^2) ≤
      ∑ u : PolyIdx d, ∑ v : PolyIdx d,
        (qRaw w.1 h J u v-∫ z, qRaw z.1 h J u v ∂experiment P n m)^2 := by
    have hb := rectangular_symmetrization_energy_le
      (fun u v : PolyIdx d => qRaw w.1 h J u v-∫ z, qRaw z.1 h J u v ∂experiment P n m)
    convert hb using 1
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    rw [hmean]
    unfold qHat
    congr 1
    ring
  have hR : (∫ w, ∑ u : PolyIdx d, (rHat w.1 h J u-rBar P n m h J u)^2 ∂experiment P n m) ≤ q*K*V := by
    rw [integral_finsetSum _ (fun u _ => hiR u)]
    calc
      _ ≤ ∑ u : PolyIdx d, K*V := Finset.sum_le_sum (fun u _ => (hr u).2)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; dsimp [q]; ring
  have hQ : (∫ w, ∑ u : PolyIdx d, ∑ v : PolyIdx d,
      (qHat w.1 h J u v-qPop P n m h J u v)^2 ∂experiment P n m) ≤ q*q*K*V := by
    calc
      _ ≤ ∫ w, ∑ u : PolyIdx d, ∑ v : PolyIdx d,
          (qRaw w.1 h J u v-∫ z, qRaw z.1 h J u v ∂experiment P n m)^2 ∂experiment P n m :=
        integral_mono (integrable_finsetSum _ (fun u _ => integrable_finsetSum _ (fun v _ => hiQ u v)))
          (integrable_finsetSum _ (fun u _ => integrable_finsetSum _ (fun v _ => hiRaw u v))) hsym
      _ = ∑ u : PolyIdx d, ∑ v : PolyIdx d, ∫ w,
          (qRaw w.1 h J u v-∫ z, qRaw z.1 h J u v ∂experiment P n m)^2 ∂experiment P n m := by
        rw [integral_finsetSum _ (fun u _ => integrable_finsetSum _ (fun v _ => hiRaw u v))]
        apply Finset.sum_congr rfl
        intro u _
        exact integral_finsetSum _ (fun v _ => hiRaw u v)
      _ ≤ ∑ u : PolyIdx d, ∑ v : PolyIdx d, K*V :=
        Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => (hq u v).2))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; dsimp [q]; ring
  change _ ≤ ((q+q*q+1)*K)*V
  calc
    _ ≤ q*K*V + q*q*K*V := add_le_add hR hQ
    _ ≤ _ := by nlinarith only [mul_nonneg hK.le hV]

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
