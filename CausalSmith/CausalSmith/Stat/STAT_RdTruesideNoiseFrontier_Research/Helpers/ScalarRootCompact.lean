module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.ScalarRootCore

/-!
# Compact scalar root analysis

Monotonicity, uniqueness, and uniform comparisons for the compact-branch scalar equation.
-/

@[expose] public section

noncomputable section
open Set
open scoped Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier

/-- The left side of the compact scalar equation. Given [the displayed inputs and assumptions](hyp:β,σ,τ), [this definition specifies the stated object](goal). -/
@[no_expose]
def compactScalarLhs (β σ τ : ℝ) : ℝ :=
  2 * (2 * β + 1) * Real.log τ + τ * (1 + Real.log (σ ^ 2 * τ))

/-- Above the compact interface, the compact scalar left side is strictly increasing. Given [the displayed inputs and assumptions](hyp:β,σ,hβ,hspos), [the stated mathematical conclusion holds](goal). -/
lemma compactScalarLhs_strictMonoOn (β σ : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hspos : 0 < σ) : StrictMonoOn (compactScalarLhs β σ) (Ioi (σ ^ (-2 : ℝ))) := by
  intro x hx y hy hxy
  have hs2pos : 0 < σ ^ 2 := sq_pos_of_pos hspos
  have hbase : σ ^ 2 * σ ^ (-2 : ℝ) = 1 := by
    rw [← Real.rpow_natCast σ 2, ← Real.rpow_add hspos]
    norm_num
  have hx' : σ ^ (-2 : ℝ) < x := hx
  have hy' : σ ^ (-2 : ℝ) < y := hy
  have hxpos : 0 < x := (Real.rpow_pos_of_pos hspos _).trans hx'
  have hypos : 0 < y := hxpos.trans hxy
  have hax : 1 < σ ^ 2 * x := by
    calc 1 = σ ^ 2 * σ ^ (-2 : ℝ) := hbase.symm
         _ < σ ^ 2 * x := mul_lt_mul_of_pos_left hx' hs2pos
  have hay : 1 < σ ^ 2 * y := by
    calc 1 = σ ^ 2 * σ ^ (-2 : ℝ) := hbase.symm
         _ < σ ^ 2 * y := mul_lt_mul_of_pos_left hy' hs2pos
  have hlogxy : Real.log x < Real.log y := Real.strictMonoOn_log hxpos hypos hxy
  have hlogaxy : Real.log (σ ^ 2 * x) < Real.log (σ ^ 2 * y) :=
    Real.strictMonoOn_log (mul_pos hs2pos hxpos) (mul_pos hs2pos hypos)
      (mul_lt_mul_of_pos_left hxy hs2pos)
  have hfactorx : 0 < 1 + Real.log (σ ^ 2 * x) := by
    have := Real.log_pos hax
    linarith
  have hfactory : 0 < 1 + Real.log (σ ^ 2 * y) := by
    have := Real.log_pos hay
    linarith
  have hmul : x * (1 + Real.log (σ ^ 2 * x)) <
      y * (1 + Real.log (σ ^ 2 * y)) := by
    calc
      x * (1 + Real.log (σ ^ 2 * x)) < y * (1 + Real.log (σ ^ 2 * x)) :=
        mul_lt_mul_of_pos_right hxy hfactorx
      _ < y * (1 + Real.log (σ ^ 2 * y)) :=
        mul_lt_mul_of_pos_left (by linarith) hypos
  have hcoef : 0 < 2 * (2 * β + 1) := by linarith [hβ.1]
  unfold compactScalarLhs
  nlinarith [mul_lt_mul_of_pos_left hlogxy hcoef]

/-- The compact scalar equation has at most one solution above the compact interface. Given [the displayed inputs and assumptions](hyp:β,n,σ,τ,τ',hβ,hspos,hτ,hτ',heq,heq'), [the stated mathematical conclusion holds](goal). -/
lemma compactScalar_unique (β n σ τ τ' : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hspos : 0 < σ) (hτ : σ ^ (-2 : ℝ) < τ) (hτ' : σ ^ (-2 : ℝ) < τ')
    (heq : 2 * (2 * β + 1) * Real.log τ +
      τ * (1 + Real.log (σ ^ 2 * τ)) = Real.log n + 1)
    (heq' : 2 * (2 * β + 1) * Real.log τ' +
      τ' * (1 + Real.log (σ ^ 2 * τ')) = Real.log n + 1) : τ' = τ := by
  apply (compactScalarLhs_strictMonoOn β σ hβ hspos).injOn hτ' hτ
  simpa [compactScalarLhs] using heq'.trans heq.symm

/-- A solution of the compact scalar equation is uniformly comparable to its
explicit logarithmic proxy. Given [the displayed inputs and assumptions](hyp:β,n,σ,τ,hβ,hn,hspos,hsone,hτ,heq), [the stated mathematical conclusion holds](goal). -/
lemma compactScalar_bounds (β n σ τ : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hn : 1 < n) (hspos : 0 < σ) (hsone : σ ≤ 1)
    (hτ : σ ^ (-2 : ℝ) < τ)
    (heq : 2 * (2 * β + 1) * Real.log τ +
      τ * (1 + Real.log (σ ^ 2 * τ)) = Real.log n + 1) :
    let B := 1 + Real.log n
    let D := Real.log (Real.exp 1 + σ ^ 2 * B)
    (1 / (2 * (1 + 2 * (2 * β + 1)))) * (B / D) ≤ τ ∧
      τ ≤ (Real.exp 1 + 6) * (B / D) := by
  dsimp only
  let B := 1 + Real.log n
  let a := σ ^ 2
  let y := a * τ
  let q := B / τ
  let J := 1 + Real.log y
  let D := Real.log (Real.exp 1 + a * B)
  have hνpos : 0 < 2 * β + 1 := by linarith [hβ.1]
  have hνle : 2 * β + 1 ≤ 3 := by linarith [hβ.2]
  have ha : 0 < a := by dsimp [a]; positivity
  have hsInv : 1 ≤ σ ^ (-2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hspos hsone (by norm_num)
  have hτone : 1 < τ := hsInv.trans_lt hτ
  have hτpos : 0 < τ := zero_lt_one.trans hτone
  have hyone : 1 < y := by
    dsimp [y, a]
    have hbase : σ ^ 2 * σ ^ (-2 : ℝ) = 1 := by
      rw [← Real.rpow_natCast σ 2, ← Real.rpow_add hspos]
      norm_num
    calc
      1 = σ ^ 2 * σ ^ (-2 : ℝ) := hbase.symm
      _ < σ ^ 2 * τ := mul_lt_mul_of_pos_left hτ (sq_pos_of_pos hspos)
  have hypos : 0 < y := zero_lt_one.trans hyone
  have hJone : 1 < J := by dsimp [J]; linarith [Real.log_pos hyone]
  have hB : 1 < B := by dsimp [B]; linarith [Real.log_pos hn]
  have hqeq : q = 2 * (2 * β + 1) * Real.log τ / τ + J := by
    dsimp [q, B, J, y, a]
    field_simp [hτpos.ne'] at heq ⊢
    nlinarith
  have hlogτnonneg : 0 ≤ Real.log τ := Real.log_nonneg hτone.le
  have hlogτle : Real.log τ ≤ τ :=
    (Real.log_le_sub_one_of_pos hτpos).trans (by linarith)
  have hJq : J ≤ q := by
    rw [hqeq]
    have : 0 ≤ 2 * (2 * β + 1) * Real.log τ / τ := by
      exact div_nonneg (mul_nonneg (by nlinarith) hlogτnonneg) hτpos.le
    linarith
  have hqJ : q ≤ 2 * (2 * β + 1) + J := by
    rw [hqeq]
    have hratio : Real.log τ / τ ≤ 1 := (div_le_one hτpos).2 hlogτle
    have := mul_le_mul_of_nonneg_left hratio (by nlinarith : 0 ≤ 2 * (2 * β + 1))
    calc
      2 * (2 * β + 1) * Real.log τ / τ + J =
          2 * (2 * β + 1) * (Real.log τ / τ) + J := by ring
      _ ≤ 2 * (2 * β + 1) * 1 + J := by simpa [add_comm] using add_le_add_right this J
      _ = 2 * (2 * β + 1) + J := by ring
  have hqone : 1 < q := hJone.trans_le hJq
  have haB : a * B = y * q := by
    dsimp [a, B, y, q]
    field_simp [hτpos.ne']
  have hDpos : 0 < D := by
    dsimp [D]
    apply Real.log_pos
    have hexp : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    have haBpos : 0 < a * B := mul_pos ha (zero_lt_one.trans hB)
    linarith
  have hD_ge_one : 1 ≤ D := by
    dsimp [D]
    rw [← Real.log_exp 1]
    apply Real.strictMonoOn_log.monotoneOn
    · exact Real.exp_pos 1
    · change 0 < Real.exp (Real.log (Real.exp 1)) + a * B
      rw [Real.exp_log (Real.exp_pos 1)]
      exact add_pos (Real.exp_pos 1) (mul_pos ha (zero_lt_one.trans hB))
    · have hab : 0 ≤ a * B := mul_nonneg ha.le (zero_lt_one.trans hB).le
      simpa using add_le_add_left hab (Real.exp 1)
  have hD_ge_logy : Real.log y ≤ D := by
    dsimp [D]
    apply Real.strictMonoOn_log.monotoneOn hypos
    · exact add_pos (Real.exp_pos 1) (mul_pos ha (zero_lt_one.trans hB))
    · rw [haB]
      have : y ≤ y * q := by nlinarith [mul_lt_mul_of_pos_left hqone hypos]
      linarith [Real.exp_pos 1]
  have hJ_le_twoD : J ≤ 2 * D := by
    dsimp [J]
    linarith
  have hq_le : q ≤ (1 + 2 * (2 * β + 1)) * J := by
    calc
      q ≤ 2 * (2 * β + 1) + J := hqJ
      _ ≤ (1 + 2 * (2 * β + 1)) * J := by nlinarith [hJone.le, hνpos]
  have hD_le : D ≤ (Real.exp 1 + 6) * J := by
    have hq7 : q ≤ J + 6 := by linarith
    have harg : Real.exp 1 + a * B ≤ y * (Real.exp 1 + J + 6) := by
      rw [haB]
      have hey : Real.exp 1 ≤ y * Real.exp 1 := by
        nlinarith [Real.exp_pos 1, hyone]
      nlinarith [mul_le_mul_of_nonneg_left hq7 hypos.le]
    have hlogarg := Real.strictMonoOn_log.monotoneOn
      (by positivity : 0 < Real.exp 1 + a * B)
      (by positivity : 0 < y * (Real.exp 1 + J + 6)) harg
    have hsumpos : 0 < Real.exp 1 + J + 6 := by positivity
    have hlogsum : Real.log (Real.exp 1 + J + 6) ≤ Real.exp 1 + J + 5 := by
      convert Real.log_le_sub_one_of_pos hsumpos using 1 <;> ring
    have hlogmul : Real.log (y * (Real.exp 1 + J + 6)) =
        Real.log y + Real.log (Real.exp 1 + J + 6) :=
      Real.log_mul hypos.ne' hsumpos.ne'
    dsimp [D] at hlogarg ⊢
    rw [hlogmul] at hlogarg
    dsimp [J] at hJone ⊢
    nlinarith [Real.exp_pos 1, hlogsum]
  have hBpos : 0 < B := zero_lt_one.trans hB
  have hqpos : 0 < q := zero_lt_one.trans hqone
  have hcoefpos : 0 < 2 * (1 + 2 * (2 * β + 1)) := by nlinarith
  constructor
  · have hqD : q ≤ 2 * (1 + 2 * (2 * β + 1)) * D := by
      calc
        q ≤ (1 + 2 * (2 * β + 1)) * J := hq_le
        _ ≤ (1 + 2 * (2 * β + 1)) * (2 * D) :=
          mul_le_mul_of_nonneg_left hJ_le_twoD (by nlinarith)
        _ = 2 * (1 + 2 * (2 * β + 1)) * D := by ring
    have hBD : B ≤ τ * (2 * (1 + 2 * (2 * β + 1)) * D) := by
      have hx := (div_le_iff₀ hτpos).mp (by simpa [q] using hqD)
      simpa [mul_assoc, mul_left_comm, mul_comm] using hx
    calc
      (1 / (2 * (1 + 2 * (2 * β + 1)))) * (B / D) =
          B / (2 * (1 + 2 * (2 * β + 1)) * D) := by field_simp
      _ ≤ τ := (div_le_iff₀ (mul_pos hcoefpos hDpos)).2 (by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hBD)
  · have hDq : D ≤ (Real.exp 1 + 6) * q :=
      hD_le.trans (mul_le_mul_of_nonneg_left hJq (by positivity))
    have hDB : D * τ ≤ (Real.exp 1 + 6) * B := by
      have hx : D ≤ ((Real.exp 1 + 6) * B) / τ := by
        calc
          D ≤ (Real.exp 1 + 6) * q := hDq
          _ = ((Real.exp 1 + 6) * B) / τ := by dsimp [q]; ring
      exact (le_div_iff₀ hτpos).mp hx
    change τ ≤ (Real.exp 1 + 6) * (B / D)
    calc
      τ ≤ ((Real.exp 1 + 6) * B) / D :=
        (le_div_iff₀ hDpos).2 (by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hDB)
      _ = (Real.exp 1 + 6) * (B / D) := by ring

/-- Raising a positive two-sided compact-scale comparison to the negative
Hölder exponent reverses its inequalities and inverts the proxy. Given [the displayed inputs and assumptions](hyp:β,B,D,τ,c,C,hβ,hB,hD,hτ,hc,hC,hlo,hhi), [the stated mathematical conclusion holds](goal). -/
lemma compactPower_bounds (β B D τ c C : ℝ) (hβ : 0 < β)
    (hB : 0 < B) (hD : 0 < D) (hτ : 0 < τ) (hc : 0 < c) (hC : 0 < C)
    (hlo : c * (B / D) ≤ τ) (hhi : τ ≤ C * (B / D)) :
    C ^ (-2 * β) * (D / B) ^ (2 * β) ≤ τ ^ (-2 * β) ∧
      τ ^ (-2 * β) ≤ c ^ (-2 * β) * (D / B) ^ (2 * β) := by
  have hR : 0 < B / D := div_pos hB hD
  have hp : -2 * β ≤ 0 := by linarith
  have hinv : (B / D) ^ (-2 * β) = (D / B) ^ (2 * β) := by
    rw [show -2 * β = -(2 * β) by ring,
      Real.div_rpow hB.le hD.le, Real.div_rpow hD.le hB.le,
      Real.rpow_neg hB.le, Real.rpow_neg hD.le]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hB _),
      ne_of_gt (Real.rpow_pos_of_pos hD _)]
  constructor
  · have hpow := Real.rpow_le_rpow_of_nonpos hτ hhi hp
    rw [Real.mul_rpow hC.le hR.le, hinv] at hpow
    exact hpow
  · have hpow := Real.rpow_le_rpow_of_nonpos (mul_pos hc hR) hlo hp
    rw [Real.mul_rpow hc.le hR.le, hinv] at hpow
    exact hpow

end CausalSmith.Stat.RdTruesideNoiseFrontier
