module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.TreeCount
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# Summation of the labeled-root tree envelope

The numerical steps MC34–MC37: a binomial/factorial estimate and a
polynomial geometric-series bound under the small-occupancy condition.
These estimates do not assert the geometric component count or the
Hellinger product assembly, which remain separate obligations.
-/

public section

open scoped BigOperators
open MeasureTheory
noncomputable section
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- The binomial coefficient and rooted-parent count have an exponential envelope.  Given [the specified input N](hyp:N), [the specified input p](hyp:p), [the specified input hp](hyp:hp), [the binomial rooted tree bound conclusion](goal) holds. -/
lemma binomial_rooted_tree_bound (N p : ℕ) (hp : 2 ≤ p) :
    (Nat.choose (N-1) (p-1) : ℝ) * (p:ℝ)^(p-1) ≤
      (N:ℝ)^(p-1) * Real.exp (p:ℝ) := by
  have hchoose : (Nat.choose (N-1) (p-1) : ℝ) ≤
      (N:ℝ)^(p-1) / (Nat.factorial (p-1):ℝ) := by
    apply (Nat.choose_le_pow_div (p-1) (N-1)).trans
    gcongr
    exact_mod_cast Nat.sub_le N 1
  calc
    _ ≤ ((N:ℝ)^(p-1) / (Nat.factorial (p-1):ℝ)) * (p:ℝ)^(p-1) :=
      mul_le_mul_of_nonneg_right hchoose (by positivity)
    _ = (N:ℝ)^(p-1) * ((p:ℝ)^(p-1) / (Nat.factorial (p-1):ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (factorial_tree_bound p hp) (by positivity)

/-- A finite polynomial-geometric sum has a bound linear in its small ratio.  Given [the specified input M](hyp:M), [the specified input z](hyp:z), [the specified input hz](hyp:hz), [the specified input hzhalf](hyp:hzhalf), [the finite tree series bound conclusion](goal) holds. -/
lemma finite_tree_series_bound (M : ℕ) (z : ℝ) (hz : 0 ≤ z) (hzhalf : z ≤ 1/2) :
    (∑ j ∈ Finset.range M, ((j+2:ℕ):ℝ)^4 * z^(j+1)) ≤
      z * ∑' j : ℕ, ((j+2:ℕ):ℝ)^4 * (1/2:ℝ)^j := by
  calc
    _ ≤ ∑ j ∈ Finset.range M, z * (((j+2:ℕ):ℝ)^4 * (1/2:ℝ)^j) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [pow_succ z]
      have hpow := pow_le_pow_left₀ hz hzhalf j
      nlinarith [mul_le_mul_of_nonneg_left hpow
        (mul_nonneg hz (by positivity : 0 ≤ ((j+2:ℕ):ℝ)^4))]
    _ = z * ∑ j ∈ Finset.range M, ((j+2:ℕ):ℝ)^4 * (1/2:ℝ)^j := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (tree_series_summable.sum_le_tsum (Finset.range M) (fun j hj => by positivity)) hz

/-- One summand of the tree envelope is controlled by its occupancy ratio.  Given [the specified input N](hyp:N), [the specified input j](hyp:j), [the specified input K](hyp:K), [the specified input v](hyp:v), [the specified input hK](hyp:hK), [the specified input hv](hyp:hv), [the tree envelope term bound conclusion](goal) holds. -/
lemma tree_envelope_term_bound (N j : ℕ) (K v : ℝ) (hK : 0 ≤ K) (hv : 0 ≤ v) :
    K^(j+2) * ((j+2:ℕ):ℝ)^4 * (Nat.choose (N-1) (j+1):ℝ) *
        ((j+2:ℕ):ℝ)^(j+1) * v^(j+1) ≤
      K * Real.exp 1 * ((j+2:ℕ):ℝ)^4 * (K * Real.exp 1 * N * v)^(j+1) := by
  have ht := binomial_rooted_tree_bound N (j+2) (by omega)
  simp only [show j+2-1 = j+1 by omega] at ht
  have he : Real.exp ((j+2:ℕ):ℝ) = Real.exp 1 * (Real.exp 1)^(j+1) := by
    rw [show ((j+2:ℕ):ℝ) = 1 + ((j+1:ℕ):ℝ)*1 by push_cast; ring,
      Real.exp_add, Real.exp_nat_mul]
  calc
    _ = (K^(j+2) * ((j+2:ℕ):ℝ)^4 * v^(j+1)) *
        ((Nat.choose (N-1) (j+1):ℝ) * ((j+2:ℕ):ℝ)^(j+1)) := by ring
    _ ≤ (K^(j+2) * ((j+2:ℕ):ℝ)^4 * v^(j+1)) *
        ((N:ℝ)^(j+1) * Real.exp ((j+2:ℕ):ℝ)) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by rw [he, show j+2 = (j+1)+1 by omega, pow_succ]; simp only [mul_pow]; ring

/-- Small occupancy controls the entire tree envelope uniformly in the truncation
and total number of records. This is the numerical content of MC35–MC37.  Given [the specified input d](hyp:d), [the specified input K](hyp:K), [the specified input hK](hyp:hK), [the tree envelope sum bound conclusion](goal) holds. -/
lemma tree_envelope_sum_bound (d : ℕ) (K : ℝ) (hK : 0 < K) :
    ∃ c0 C : ℝ, 0 < c0 ∧ 0 < C ∧ ∀ (N M : ℕ) (delta : ℝ),
      0 ≤ delta → (N:ℝ)*delta^d ≤ c0 →
      (∑ j ∈ Finset.range M,
        K^(j+2) * ((j+2:ℕ):ℝ)^4 * (Nat.choose (N-1) (j+1):ℝ) *
          ((j+2:ℕ):ℝ)^(j+1) * ((4*delta)^d)^(j+1)) ≤ C*(N:ℝ)*delta^d := by
  let S : ℝ := ∑' j : ℕ, ((j+2:ℕ):ℝ)^4 * (1/2:ℝ)^j
  have hS : 0 ≤ S := by
    simpa only [Finset.sum_empty] using
      tree_series_summable.sum_le_tsum (∅ : Finset ℕ) (fun j hj => by positivity)
  let E : ℝ := K * Real.exp 1 * (4:ℝ)^d
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨1/(2*E), (S+1)*(K*Real.exp 1)^2*(4:ℝ)^d,
    by positivity, by positivity, ?_⟩
  intro N M delta hd hocc
  let z : ℝ := E * (N:ℝ) * delta^d
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hzhalf : z ≤ 1/2 := by
    have ht := mul_le_mul_of_nonneg_left hocc hE.le
    have hid : E*(1/(2*E)) = 1/2 := by field_simp
    simpa only [hid, z, mul_assoc] using ht
  have hbase : K * Real.exp 1 * (N:ℝ) * (4*delta)^d = z := by
    dsimp [z, E]
    rw [mul_pow]
    ring
  calc
    _ ≤ ∑ j ∈ Finset.range M,
        K * Real.exp 1 * ((j+2:ℕ):ℝ)^4 * z^(j+1) := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [hbase] using tree_envelope_term_bound N j K ((4*delta)^d)
        hK.le (by positivity)
    _ = K * Real.exp 1 * (∑ j ∈ Finset.range M, ((j+2:ℕ):ℝ)^4 * z^(j+1)) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ ≤ K * Real.exp 1 * (z*S) := mul_le_mul_of_nonneg_left
      (finite_tree_series_bound M z hz hzhalf) (by positivity)
    _ ≤ K * Real.exp 1 * (z*(S+1)) := by gcongr; linarith
    _ = _ := by dsimp [z, E]; ring

/-- Applying the geometric count lemma to the numerical envelope gives the
labeled-root factor nN, uniformly in the auxiliary-to-labeled ratio.
The geometric count itself is a separate, currently unfinished dependency.  Given [the specified input d](hyp:d), [the specified input K](hyp:K), [the specified input hK](hyp:hK), [the labeled component series bound conclusion](goal) holds. -/
lemma labeled_component_series_bound (d : ℕ) (K : ℝ) (hK : 0 < K) :
    ∃ c0 C : ℝ, 0 < c0 ∧ 0 < C ∧ ∀ (n m : ℕ) (h delta : ℝ),
      0 < h → h ≤ 1/2 → 0 < delta → delta ≤ h →
      ((n:ℝ)+m)*delta^d ≤ c0 →
      (∑ j ∈ Finset.range (n+m), K^(j+2) * ((j+2:ℕ):ℝ)^4 *
        (∫ x : Fin (n+m) → Cov d,
          ((Finset.univ.filter (fun c : (recordGraph h delta x).ConnectedComponent =>
            (componentVertices h delta x c).card = j+2 ∧
            ∃ i ∈ componentVertices h delta x c, i.val < n)).card : ℝ)
          ∂Measure.pi (fun _ : Fin (n+m) => uniformLaw d))) ≤
        C*(n:ℝ)*((n:ℝ)+m)*h^d*delta^d := by
  obtain ⟨c0, C, hc0, hC, hsum⟩ := tree_envelope_sum_bound d K hK
  refine ⟨c0, C, hc0, hC, ?_⟩
  intro n m h delta hh hhhalf hd hdh hocc
  have hb := hsum (n+m) (n+m) delta hd.le (by simpa only [Nat.cast_add] using hocc)
  calc
    _ ≤ ∑ j ∈ Finset.range (n+m),
        ((n:ℝ)*h^d) * (K^(j+2) * ((j+2:ℕ):ℝ)^4 *
          (Nat.choose (n+m-1) (j+1):ℝ) * ((j+2:ℕ):ℝ)^(j+1) *
            ((4*delta)^d)^(j+1)) := by
      apply Finset.sum_le_sum
      intro j hj
      have ht := labeled_root_tree_count d n m h delta hh hhhalf hd hdh (j+2) (by omega)
      simp only [show j+2-1 = j+1 by omega] at ht
      have hm := mul_le_mul_of_nonneg_left ht
        (by positivity : 0 ≤ K^(j+2) * ((j+2:ℕ):ℝ)^4)
      convert hm using 1 <;> ring
    _ = ((n:ℝ)*h^d) * (∑ j ∈ Finset.range (n+m),
        K^(j+2) * ((j+2:ℕ):ℝ)^4 * (Nat.choose (n+m-1) (j+1):ℝ) *
          ((j+2:ℕ):ℝ)^(j+1) * ((4*delta)^d)^(j+1)) := by rw [Finset.mul_sum]
    _ ≤ ((n:ℝ)*h^d) * (C*(n+m:ℕ)*delta^d) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by push_cast; ring

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
