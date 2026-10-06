module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.GaussianLikelihood
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.Rate
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.MarkedDomination
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.MarkedCells
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.ObservedCellDensity

/-!
# True-side Gaussian measurement-error endpoint frontier

Helpers/Law-level constructions and the obligations specified by the typed core.
Cited logical facts are explicit inputs; bibliographic records have no logical consumers.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier


/-- All cancellation and full-domain legality assertions for the actual alternative laws. Given [the displayed inputs and assumptions](hyp:β,b,σ,m,hβ,hb,hm), [the stated mathematical conclusion holds](goal). -/
-- @node: lem:legal-cancellation
lemma legal_cancellation (β b σ : ℝ) (m : ℕ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hb : b ∈ Ioc (0 : ℝ) 1) -- @realizes b(real support width with 0 < b and b ≤ 1)
    (hm : 2 ≤ m) :
    block m 0 = 1 ∧ block m 1 = 0 ∧
    (∀ t ∈ Icc (0 : ℝ) 1, |block m t| ≤ 1) ∧
    (∫ t in (0 : ℝ)..1, (block m t)^2) ≤ 1 / blockNorm m ∧
    (∀ k : ℕ, k ≤ m-2 → (∫ t in (0 : ℝ)..1, t^k * block m t) = 0) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, |deriv (block m) t| ≤ 7 * (m : ℝ)^2) ∧
    holderSeminorm β (legalExtension b m) ≤ ENNReal.ofReal (7 * (b/(m : ℝ)^2) ^ (-β)) ∧
    (∀ s : Bool, Model β σ (altLaw classicalLegendreFacts β b m s hβ hb hm)) ∧
    |theta (altLaw classicalLegendreFacts β b m true hβ hb hm) -
      theta (altLaw classicalLegendreFacts β b m false hβ hb hm)| =
      2 * kappa * (b/(m : ℝ)^2)^β := by
  let legendre_of_gate : ClassicalLegendreFacts := classicalLegendreFacts
  refine ⟨block_zero legendre_of_gate m, block_one m, block_abs_le_one legendre_of_gate m, ?_⟩
  refine ⟨block_sq_integral_le legendre_of_gate m, ?_⟩
  refine ⟨fun k hk => block_moment_zero legendre_of_gate m k hm hk,
    block_deriv_bound legendre_of_gate m hm, ?_⟩
  refine ⟨legalExtension_holder_bound legendre_of_gate β b m hβ hb.1 hm, ?_,
    altLaw_separation legendre_of_gate β b m hβ hb hm⟩
  exact fun s => altLaw_model legendre_of_gate β b σ m s hβ hb hm
/-- The factorial likelihood tail. Given [the displayed inputs and assumptions](hyp:b,σ,m), [this definition specifies the stated object](goal). -/
def likelihoodTail (b σ : ℝ) (m : ℕ) : ℝ :=
  ∑' j : ℕ, if m-1 ≤ j then likelihoodLambda b σ ^ j / (Nat.factorial j : ℝ) else 0
/-- The factorial likelihood tail is absolutely convergent at every support and noise scale. Given [the displayed inputs and assumptions](hyp:b,σ,m), [the stated mathematical conclusion holds](goal). -/
lemma likelihoodTail_summable (b σ : ℝ) (m : ℕ) :
    Summable (fun j : ℕ => if m-1 ≤ j then
      likelihoodLambda b σ ^ j / (Nat.factorial j : ℝ) else 0) := by
  have hlam : 0 ≤ likelihoodLambda b σ := by
    unfold likelihoodLambda
    positivity
  apply (Real.summable_pow_div_factorial (likelihoodLambda b σ)).of_norm_bounded
  intro j
  have hj : 0 ≤ likelihoodLambda b σ ^ j / (Nat.factorial j : ℝ) := by positivity
  split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg hlam, hj]

/-- The convergent factorial likelihood tail is nonnegative. Given [the displayed inputs and assumptions](hyp:b,σ,m), [the stated mathematical conclusion holds](goal). -/
lemma likelihoodTail_nonneg (b σ : ℝ) (m : ℕ) : 0 ≤ likelihoodTail b σ m := by
  apply tsum_nonneg
  intro j
  unfold likelihoodLambda
  split_ifs <;> positivity

/-- The retained likelihood terms are bounded by the full exponential series. Given [the displayed inputs and assumptions](hyp:b,σ,m), [the stated mathematical conclusion holds](goal). -/
lemma likelihoodTail_le_exp (b σ : ℝ) (m : ℕ) :
    likelihoodTail b σ m ≤ Real.exp (likelihoodLambda b σ) := by
  have hlam : 0 ≤ likelihoodLambda b σ := by unfold likelihoodLambda; positivity
  have hseries : HasSum (fun j : ℕ => likelihoodLambda b σ ^ j / (Nat.factorial j : ℝ))
      (Real.exp (likelihoodLambda b σ)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have hbound := tsum_of_norm_bounded hseries (f := fun j : ℕ =>
      if m-1 ≤ j then likelihoodLambda b σ ^ j / (Nat.factorial j : ℝ) else 0) (by
    intro j
    have hj : 0 ≤ likelihoodLambda b σ ^ j / (Nat.factorial j : ℝ) := by positivity
    split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg hlam, hj])
  change ‖likelihoodTail b σ m‖ ≤ Real.exp (likelihoodLambda b σ) at hbound
  simpa only [Real.norm_eq_abs, abs_of_nonneg (likelihoodTail_nonneg b σ m)] using hbound

/-- Above an index whose successor dominates twice the argument, factorial terms
are bounded by a geometric sequence with ratio one half. Given [the displayed inputs and assumptions](hyp:z,N,k,hz,hsmall), [the stated mathematical conclusion holds](goal). -/
lemma factorial_tail_term_le_geometric (z : ℝ) (N k : ℕ) (hz : 0 ≤ z)
    (hsmall : z ≤ ((N : ℝ) + 1) / 2) :
    z^(k+N) / (Nat.factorial (k+N) : ℝ) ≤
      (z^N / (Nat.factorial N : ℝ)) * (1/2 : ℝ)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hden : (0 : ℝ) < k+N+1 := by positivity
    have hratio : z / ((k+N : ℕ) + 1 : ℝ) ≤ 1/2 := by
      rw [div_le_iff₀ (by positivity)]
      push_cast
      linarith [show (0 : ℝ) ≤ k by positivity]
    have hrec : z^(k+1+N) / (Nat.factorial (k+1+N) : ℝ) =
        (z^(k+N) / (Nat.factorial (k+N) : ℝ)) *
          (z / ((k+N : ℕ) + 1 : ℝ)) := by
      rw [show k+1+N = (k+N)+1 by omega, Nat.factorial_succ, pow_succ]
      push_cast
      field_simp
    rw [hrec, pow_succ]
    calc
      _ ≤ (z^N / (Nat.factorial N : ℝ)) * (1/2 : ℝ)^k *
          (z / ((k+N : ℕ) + 1 : ℝ)) :=
        mul_le_mul_of_nonneg_right ih (by positivity)
      _ ≤ (z^N / (Nat.factorial N : ℝ)) * (1/2 : ℝ)^k * (1/2 : ℝ) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by ring

/-- Summing the geometric majorant bounds the retained likelihood tail by twice
its first term; this is the first inequality in roadmap step CE.1. Given [the displayed inputs and assumptions](hyp:b,σ,m,hsmall), [the stated mathematical conclusion holds](goal). -/
lemma likelihoodTail_le_twice_first (b σ : ℝ) (m : ℕ)
    (hsmall : likelihoodLambda b σ ≤ (((m-1 : ℕ) : ℝ)+1)/2) :
    likelihoodTail b σ m ≤
      2 * likelihoodLambda b σ^(m-1) / (Nat.factorial (m-1) : ℝ) := by
  let z := likelihoodLambda b σ
  let N := m-1
  have hz : 0 ≤ z := by unfold z likelihoodLambda; positivity
  have hshift : likelihoodTail b σ m =
      ∑' k : ℕ, z^(k+N) / (Nat.factorial (k+N) : ℝ) := by
    have hzero : (∑ j ∈ Finset.range N, if N ≤ j then
        z^j / (Nat.factorial j : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [if_neg (by have := Finset.mem_range.mp hj; omega)]
    have hs := (likelihoodTail_summable b σ m).sum_add_tsum_nat_add N
    change (∑ j ∈ Finset.range N, if N ≤ j then
      z^j / (Nat.factorial j : ℝ) else 0) +
      (∑' k : ℕ, if N ≤ k+N then z^(k+N) /
        (Nat.factorial (k+N) : ℝ) else 0) = likelihoodTail b σ m at hs
    simpa only [hzero, zero_add, Nat.le_add_left, if_true] using hs.symm
  have hmajor : Summable (fun k : ℕ =>
      (z^N / (Nat.factorial N : ℝ)) * (1/2 : ℝ)^k) :=
    summable_geometric_two.mul_left _
  have hterms := factorial_tail_term_le_geometric z N
  have hsum : Summable (fun k : ℕ => z^(k+N) / (Nat.factorial (k+N) : ℝ)) :=
    hmajor.of_nonneg_of_le (fun k => by positivity) (fun k => hterms k hz hsmall)
  rw [hshift]
  calc
    _ ≤ ∑' k : ℕ, (z^N / (Nat.factorial N : ℝ)) * (1/2 : ℝ)^k :=
      hsum.tsum_le_tsum (fun k => hterms k hz hsmall) hmajor
    _ = _ := by rw [tsum_mul_left, tsum_geometric_two]; dsimp [z, N]; ring

/-- The full observed binary-mark likelihood bound, including absolute continuity and finite density square. Given [the displayed inputs and assumptions](hyp:β,b,σ,m,hβ,hb,hm,hσ), [the stated mathematical conclusion holds](goal). -/
-- @node: lem:full-marked-likelihood
lemma full_marked_likelihood (β b σ : ℝ) (m : ℕ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m) (hσ : σ ∈ Ioc (0 : ℝ) 1) :
    let plus := Pobs (altLaw classicalLegendreFacts β b m true hβ hb hm) σ
    let minus := Pobs (altLaw classicalLegendreFacts β b m false hβ hb hm) σ
    let mid := 16 * kappa^2 * (b/(m : ℝ)^2)^(2*β) *
      ∫ w : ℝ, markedConvolution b m σ w ^ 2 / treatedConvolution σ w
    let upper := 16 * kappa^2 * (b/(m : ℝ)^2)^(2*β) * (b/blockNorm m) *
      Real.exp (b^2/(24*σ^2)) * likelihoodTail b σ m
    chiSqExt plus minus ≤ ENNReal.ofReal mid ∧ ENNReal.ofReal mid ≤ ENNReal.ofReal upper ∧
    plus ≪ minus ∧ Integrable (fun o => ((plus.rnDeriv minus o).toReal - 1)^2) minus ∧
    Integrable (fun w => markedConvolution b m σ w ^ 2 / treatedConvolution σ w) ∧
    Summable (fun j : ℕ => if m-1 ≤ j then likelihoodLambda b σ ^ j / (Nat.factorial j : ℝ) else 0) := by
  let legendre_of_gate : ClassicalLegendreFacts := classicalLegendreFacts
  refine ⟨?_, ?_, ?_, ?_,
    markedConvolution_square_div_integrable legendre_of_gate b σ m hb hσ.1,
    likelihoodTail_summable b σ m⟩
  · letI := (altLaw legendre_of_gate β b m true hβ hb hm).prob
    letI := (altLaw legendre_of_gate β b m false hβ hb hm).prob
    letI : IsProbabilityMeasure
        (Pobs (altLaw legendre_of_gate β b m true hβ hb hm) σ) :=
      Measure.isProbabilityMeasure_map (obs_measurable σ).aemeasurable
    letI : IsProbabilityMeasure
        (Pobs (altLaw legendre_of_gate β b m false hβ hb hm) σ) :=
      Measure.isProbabilityMeasure_map (obs_measurable σ).aemeasurable
    have hac := altLaw_observed_absolutelyContinuous legendre_of_gate
      β b σ m true false hβ hb hm
    have hint := altLaw_observed_likelihood_square_integrable legendre_of_gate
      β b σ m true false hβ hb hm
    rw [chiSqExt_eq_ofReal_chiSqDiv _ _ hac hint]
    apply ENNReal.ofReal_le_ofReal
    unfold Causalean.Stat.chiSqDiv
    calc
      (∫ o, (((Pobs (altLaw legendre_of_gate β b m true hβ hb hm) σ).rnDeriv
          (Pobs (altLaw legendre_of_gate β b m false hβ hb hm) σ) o).toReal - 1)^2 ∂
          Pobs (altLaw legendre_of_gate β b m false hβ hb hm) σ) =
          ∫ o, (altObservedLikelihoodRatio β b σ m o - 1)^2 ∂
            Pobs (altLaw legendre_of_gate β b m false hβ hb hm) σ := by
        apply integral_congr_ae
        exact (altLaw_observed_rnDeriv legendre_of_gate β b σ m hβ hb hm hσ.1).fun_comp
          (fun r => (r - 1)^2)
      _ = ∫ w : ℝ, ∑ y : Bool,
          (witnessTreatedCellConvolution β b σ m true y w -
            witnessTreatedCellConvolution β b σ m false y w)^2 /
              witnessTreatedCellConvolution β b σ m false y w :=
        altLikelihoodRatio_sq_integral_eq legendre_of_gate β b σ m hβ hb hm hσ.1
      _ ≤ 16 * kappa^2 * (b/(m : ℝ)^2)^(2*β) *
          ∫ w : ℝ, markedConvolution b m σ w ^ 2 / treatedConvolution σ w :=
        witnessTreatedCellConvolution_integral_bound legendre_of_gate
          β b σ m hβ hb hm hσ.1
  · apply ENNReal.ofReal_le_ofReal
    have htail := marked_square_factorial_tail_bound legendre_of_gate b σ m hb hσ.1 hm
    have hscale : 0 ≤ 16 * kappa^2 * (b/(m : ℝ)^2)^(2*β) := by
      have hbp := hb.1
      positivity
    have hh := mul_le_mul_of_nonneg_left htail hscale
    simpa only [likelihoodTail, mul_assoc] using hh
  · exact altLaw_observed_absolutelyContinuous legendre_of_gate β b σ m true false hβ hb hm
  · exact altLaw_observed_likelihood_square_integrable legendre_of_gate β b σ m true false hβ hb hm
  -- BLOCKER: identify Pobs with its full cell-density measure and rewrite the
  -- observed rnDeriv integral as the treated-cell convolution sum. ML.1 and its
  -- integrable ML.2 bound are proved in MarkedCells, but the measure bridge remains open.
/-- Positive noise yields a legal support width. Given [the displayed inputs and assumptions](hyp:σ,m,hσ,hm), [the stated mathematical conclusion holds](goal). -/
lemma noiseSupport_mem (σ : ℝ) (m : ℕ) (hσ : σ ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m) :
    noiseSupport σ m ∈ Ioc (0 : ℝ) 1 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  change 0 < min 1 (σ * Real.sqrt m / 8) ∧ min 1 (σ * Real.sqrt m / 8) ≤ 1
  exact ⟨lt_min (by norm_num) (div_pos (mul_pos hσ.1 (Real.sqrt_pos.2 hmpos))
    (by norm_num)), min_le_left _ _⟩
/-- The noise-adapted support keeps the factorial-series argument below m/256,
including the support saturation interface. Given [the displayed inputs and assumptions](hyp:σ,m,hσ,hm), [the stated mathematical conclusion holds](goal). -/
lemma noiseSupport_likelihoodLambda_le (σ : ℝ) (m : ℕ)
    (hσ : σ ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m) :
    likelihoodLambda (noiseSupport σ m) σ ≤ (m : ℝ)/256 := by
  have hb := (noiseSupport_mem σ m hσ hm).1.le
  have hsupport : noiseSupport σ m ≤ σ * Real.sqrt m / 8 := min_le_right _ _
  have hs : (noiseSupport σ m)^2 ≤ (σ * Real.sqrt m / 8)^2 :=
    pow_le_pow_left₀ hb hsupport 2
  have hroot := Real.sq_sqrt (show (0 : ℝ) ≤ m by positivity)
  have hσpos := hσ.1
  unfold likelihoodLambda
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hs]

/-- The public support's likelihood tail is at most twice its first retained term. Given [the displayed inputs and assumptions](hyp:σ,m,hσ,hm), [the stated mathematical conclusion holds](goal). -/
lemma noiseSupport_likelihoodTail_le (σ : ℝ) (m : ℕ)
    (hσ : σ ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m) :
    likelihoodTail (noiseSupport σ m) σ m ≤
      2 * likelihoodLambda (noiseSupport σ m) σ^(m-1) /
        (Nat.factorial (m-1) : ℝ) := by
  apply likelihoodTail_le_twice_first
  have hlam := noiseSupport_likelihoodLambda_le σ m hσ hm
  have hcast : ((m-1 : ℕ) : ℝ)+1 = (m : ℝ) := by
    exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ m by omega))
  rw [hcast]
  exact hlam.trans (by
    have hm0 : (0 : ℝ) ≤ m := by positivity
    linarith)

/-- Inserting CE.1 into the full marked likelihood bound retains both binary marks
and the whole real proxy domain. Given [the displayed inputs and assumptions](hyp:hleg,β,σ,m,hβ,hσ,hm), [the stated mathematical conclusion holds](goal). -/
lemma cancellation_information_first_term_bound (hleg : ClassicalLegendreFacts)
    (β σ : ℝ) (m : ℕ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hσ : σ ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m) :
    let b := noiseSupport σ m
    let h := noiseResolution σ m
    chiSqExt (Pobs (altLaw hleg β b m true hβ (noiseSupport_mem σ m hσ hm) hm) σ)
      (Pobs (altLaw hleg β b m false hβ (noiseSupport_mem σ m hσ hm) hm) σ) ≤
      ENNReal.ofReal (32 * kappa^2 * h^(2*β) * (b/blockNorm m) *
        Real.exp (b^2/(24*σ^2)) * likelihoodLambda b σ^(m-1) /
          (Nat.factorial (m-1) : ℝ)) := by
  dsimp only
  have hb := noiseSupport_mem σ m hσ hm
  have hfull := full_marked_likelihood β (noiseSupport σ m) σ m hβ hb hm hσ
  apply (hfull.1.trans hfull.2.1).trans
  apply ENNReal.ofReal_le_ofReal
  have htail := noiseSupport_likelihoodTail_le σ m hσ hm
  have hb0 : 0 ≤ noiseSupport σ m := hb.1.le
  have hcoeff : 0 ≤ 16 * kappa^2 * (noiseSupport σ m/(m : ℝ)^2)^(2*β) *
      (noiseSupport σ m/blockNorm m) * Real.exp ((noiseSupport σ m)^2/(24*σ^2)) := by
    exact mul_nonneg (mul_nonneg (by positivity)
      (div_nonneg hb.1.le (blockNorm_pos m).le)) (Real.exp_pos _).le
  have hbound := mul_le_mul_of_nonneg_left htail hcoeff
  simpa only [noiseResolution] using hbound.trans_eq (by ring)

/-- The elementary logarithmic factorial estimate in CE.1, valid at every
positive integer, follows by summing the logarithm's tangent-line inequality. Given [the displayed inputs and assumptions](hyp:N,hN), [the stated mathematical conclusion holds](goal). -/
lemma log_factorial_lower_bound (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * Real.log N - N ≤ Real.log (Nat.factorial N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hquot := Real.log_le_sub_one_of_pos (show 0 < ((N : ℝ)+1)/N by positivity)
    have hlog : (N : ℝ) * (Real.log ((N : ℝ)+1) - Real.log N) ≤ 1 := by
      rw [Real.log_div (by positivity) hNp.ne'] at hquot
      have hh := mul_le_mul_of_nonneg_left hquot hNp.le
      have hcancel : (N : ℝ) * (((N : ℝ)+1)/N - 1) = 1 := by field_simp; ring
      rwa [hcancel] at hh
    rw [Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    push_cast
    nlinarith

/-- The last inequality in CE.1: factorial decay is written in exponential form. Given [the displayed inputs and assumptions](hyp:z,N,hz,hN), [the stated mathematical conclusion holds](goal). -/
lemma factorial_term_le_log_exp (z : ℝ) (N : ℕ) (hz : 0 < z) (hN : 1 ≤ N) :
    z^N / (Nat.factorial N : ℝ) ≤
      Real.exp (-(N : ℝ) * Real.log ((N : ℝ)/(Real.exp 1 * z))) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hfac := log_factorial_lower_bound N hN
  have hlog : Real.log (z^N / (Nat.factorial N : ℝ)) ≤
      -(N : ℝ) * Real.log ((N : ℝ)/(Real.exp 1 * z)) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow,
      Real.log_div hNp.ne' (by positivity),
      Real.log_mul (by positivity) hz.ne', Real.log_exp]
    nlinarith
  have he := Real.exp_le_exp.mpr hlog
  rwa [Real.exp_log (by positivity)] at he

/-- CE.2 compares the retained factorial exponent to the uniform degree exponent. Given [the displayed inputs and assumptions](hyp:M,N,z,hM,hN,hz,hsmall), [the stated mathematical conclusion holds](goal). -/
lemma factorial_exponent_lower_bound (M N z : ℝ) (hM : 2 ≤ M)
    (hN : M/2 ≤ N) (hz : 0 < z) (hsmall : z ≤ M/256) :
    M * (1 + Real.log (M/z))/8 ≤
      N * Real.log (N/(Real.exp 1*z)) - z/6 := by
  have hMp : 0 < M := by linarith
  have hNp : 0 < N := by linarith
  have hratio : 256 ≤ M/z := (le_div_iff₀ hz).mpr (by linarith)
  have hlogr : 8 * Real.log 2 ≤ Real.log (M/z) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 256) hratio
    have hid : Real.log (256 : ℝ) = 8 * Real.log 2 := by
      rw [show (256 : ℝ) = 2^8 by norm_num, Real.log_pow]; norm_num
    rwa [hid] at hh
  have hlogtwo : (1/2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hlogN : Real.log (M/z) - Real.log 2 - 1 ≤
      Real.log (N/(Real.exp 1*z)) := by
    have hh := Real.log_le_log (show 0 < M/2 by positivity) hN
    rw [Real.log_div hMp.ne' (by norm_num)] at hh
    rw [Real.log_div hMp.ne' hz.ne', Real.log_div hNp.ne' (by positivity),
      Real.log_mul (by positivity) hz.ne', Real.log_exp]
    linarith
  have hpos : 0 ≤ Real.log (M/z) - Real.log 2 - 1 := by linarith
  have hprod := mul_le_mul hN hlogN hpos hNp.le
  have hgap : 0 ≤ (3/8 : ℝ)*Real.log (M/z) - Real.log 2/2 - 5/8 - 1/1536 := by
    linarith
  have hh := mul_nonneg hMp.le hgap
  nlinarith

/-- The support choice and CE.1--CE.2 give the exponential likelihood-tail bound CE.3. Given [the displayed inputs and assumptions](hyp:σ,m,hσ,hm), [the stated mathematical conclusion holds](goal). -/
lemma noiseSupport_likelihoodTail_exp_bound (σ : ℝ) (m : ℕ)
    (hσ : σ ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m) :
    Real.exp ((noiseSupport σ m)^2/(24*σ^2)) *
      likelihoodTail (noiseSupport σ m) σ m ≤
      2 * Real.exp (-(m : ℝ) *
        (1 + Real.log ((m : ℝ)/likelihoodLambda (noiseSupport σ m) σ))/8) := by
  let z := likelihoodLambda (noiseSupport σ m) σ
  have hbp := (noiseSupport_mem σ m hσ hm).1
  have hσp := hσ.1
  have hz : 0 < z := by dsimp [z, likelihoodLambda]; positivity
  have hsmall := noiseSupport_likelihoodLambda_le σ m hσ hm
  have hN : 1 ≤ m-1 := by omega
  have hcast : ((m-1 : ℕ) : ℝ)+1 = (m : ℝ) := by
    exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ m by omega))
  have hNhalf : (m : ℝ)/2 ≤ ((m-1 : ℕ) : ℝ) := by
    have hh : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hexponent := factorial_exponent_lower_bound (m : ℝ) ((m-1 : ℕ) : ℝ) z
    (by exact_mod_cast hm) hNhalf hz hsmall
  have hscale : (noiseSupport σ m)^2/(24*σ^2) = z/6 := by
    dsimp [z, likelihoodLambda]; ring
  rw [hscale]
  calc
    _ ≤ Real.exp (z/6) * (2 * z^(m-1) / (Nat.factorial (m-1) : ℝ)) :=
      mul_le_mul_of_nonneg_left (noiseSupport_likelihoodTail_le σ m hσ hm) (by positivity)
    _ ≤ Real.exp (z/6) * (2 * Real.exp (-((m-1 : ℕ) : ℝ) *
        Real.log (((m-1 : ℕ) : ℝ)/(Real.exp 1*z)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hh := mul_le_mul_of_nonneg_left (factorial_term_le_log_exp z (m-1) hz hN)
        (by norm_num : (0 : ℝ) ≤ 2)
      simpa only [mul_div_assoc] using hh
    _ = 2 * Real.exp (z/6 - ((m-1 : ℕ) : ℝ) *
        Real.log (((m-1 : ℕ) : ℝ)/(Real.exp 1*z))) := by
      rw [sub_eq_add_neg, Real.exp_add]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      linarith

/-- The block normalization converts support mass into one resolution factor. Given [the displayed inputs and assumptions](hyp:σ,m,hσ,hm), [the stated mathematical conclusion holds](goal). -/
lemma noiseSupport_div_blockNorm_le (σ : ℝ) (m : ℕ)
    (hσ : σ ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m) :
    noiseSupport σ m / blockNorm m ≤ noiseResolution σ m / 3 := by
  have hb := (noiseSupport_mem σ m hσ hm).1.le
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnorm : 3*(m : ℝ)^2 ≤ blockNorm m := by
    unfold blockNorm
    nlinarith
  unfold noiseResolution
  calc
    _ ≤ noiseSupport σ m / (3*(m : ℝ)^2) :=
      div_le_div_of_nonneg_left hb (by positivity) hnorm
    _ = _ := by ring

/-- CE.4 is the full marked information bound with its factorial degree exponent. Given [the displayed inputs and assumptions](hyp:hleg,β,σ,m,hβ,hσ,hm), [the stated mathematical conclusion holds](goal). -/
lemma cancellation_information_degree_bound (hleg : ClassicalLegendreFacts)
    (β σ : ℝ) (m : ℕ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hσ : σ ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m) :
    let b := noiseSupport σ m
    let h := noiseResolution σ m
    chiSqExt (Pobs (altLaw hleg β b m true hβ (noiseSupport_mem σ m hσ hm) hm) σ)
      (Pobs (altLaw hleg β b m false hβ (noiseSupport_mem σ m hσ hm) hm) σ) ≤
      ENNReal.ofReal ((32/3 : ℝ) * kappa^2 * h^(2*β+1) *
        Real.exp (-(m : ℝ)*(1 + Real.log ((m : ℝ)/likelihoodLambda b σ))/8)) := by
  dsimp only
  have hb := noiseSupport_mem σ m hσ hm
  have hfull := full_marked_likelihood β (noiseSupport σ m) σ m hβ hb hm hσ
  apply (hfull.1.trans hfull.2.1).trans
  apply ENNReal.ofReal_le_ofReal
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hbp := hb.1
  have hhp : 0 < noiseResolution σ m := by unfold noiseResolution; positivity
  have htail := noiseSupport_likelihoodTail_exp_bound σ m hσ hm
  have hnorm := noiseSupport_div_blockNorm_le σ m hσ hm
  have hrpow : (noiseResolution σ m)^(2*β+1) =
      (noiseResolution σ m)^(2*β) * noiseResolution σ m := by
    rw [Real.rpow_add hhp, Real.rpow_one]
  change 16 * kappa^2 * (noiseResolution σ m)^(2*β) *
    (noiseSupport σ m/blockNorm m) *
    Real.exp ((noiseSupport σ m)^2/(24*σ^2)) *
    likelihoodTail (noiseSupport σ m) σ m ≤ _
  calc
    _ = (16 * kappa^2 * (noiseResolution σ m)^(2*β) *
          (noiseSupport σ m/blockNorm m)) *
        (Real.exp ((noiseSupport σ m)^2/(24*σ^2)) *
          likelihoodTail (noiseSupport σ m) σ m) := by ring
    _ ≤ (16 * kappa^2 * (noiseResolution σ m)^(2*β) *
          (noiseSupport σ m/blockNorm m)) *
        (2 * Real.exp (-(m : ℝ)*(1 +
          Real.log ((m : ℝ)/likelihoodLambda (noiseSupport σ m) σ))/8)) :=
      mul_le_mul_of_nonneg_left htail (mul_nonneg (by positivity)
        (div_nonneg hb.1.le (blockNorm_pos m).le))
    _ ≤ (16 * kappa^2 * (noiseResolution σ m)^(2*β) *
          (noiseResolution σ m/3)) *
        (2 * Real.exp (-(m : ℝ)*(1 +
          Real.log ((m : ℝ)/likelihoodLambda (noiseSupport σ m) σ))/8)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by rw [hrpow]; ring

/-- The saturated support implies the scalar threshold in CE.8. Given [the displayed inputs and assumptions](hyp:σ,m,hσ,hm,hsat), [the stated mathematical conclusion holds](goal). -/
lemma noiseSupport_saturated_threshold (σ : ℝ) (m : ℕ)
    (hσ : σ ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m)
    (hsat : 1 ≤ σ * Real.sqrt m / 8) :
    noiseSupport σ m = 1 ∧ 64 ≤ σ^2 * (m : ℝ) := by
  have hroot := Real.sq_sqrt (show (0 : ℝ) ≤ m by positivity)
  have hprod : 8 ≤ σ * Real.sqrt m := by linarith
  have hprod0 : 0 ≤ σ * Real.sqrt m := by positivity
  constructor
  · exact min_eq_left hsat
  · nlinarith [sq_nonneg (σ * Real.sqrt m - 8)]

/-- At saturated support, the compact cost formula is exact, including the
saturation equality; this is the equality in CE.8. Given [the displayed inputs and assumptions](hyp:σ,m,hσ,hm,hsat), [the stated mathematical conclusion holds](goal). -/
lemma noiseCost_saturated_eq (σ : ℝ) (m : ℕ)
    (hσ : σ ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m)
    (hsat : 1 ≤ σ * Real.sqrt m / 8) :
    1 + noiseCost (noiseResolution σ m) σ =
      (m : ℝ) * (1 + Real.log (σ^2 * (m : ℝ))) := by
  have hs := noiseSupport_saturated_threshold σ m hσ hm hsat
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hh : noiseResolution σ m = 1 / (m : ℝ)^2 := by
    unfold noiseResolution
    rw [hs.1]
  have hcompact : 1 / (m : ℝ)^2 < σ^4 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [sq_nonneg (σ^2 * (m : ℝ) - 64)]
  have hσ4 : σ^4 ≤ σ := by
    have := pow_le_pow_left₀ hσ.1.le hσ.2 3
    nlinarith [mul_le_mul_of_nonneg_left this hσ.1.le]
  have hroot : Real.sqrt (1 / (m : ℝ)^2) = 1 / (m : ℝ) := by
    rw [Real.sqrt_div (by norm_num), Real.sqrt_one, Real.sqrt_sq hmp.le]
  have hpower : (1 / (m : ℝ)^2) ^ (-1/2 : ℝ) = (m : ℝ) := by
    rw [show (-1/2 : ℝ) = -(1/2 : ℝ) by norm_num,
      Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, hroot]
    simp
  rw [hh, noiseCost, if_neg (by linarith), if_neg (not_le.mpr hcompact),
    hpower, hroot]
  simp only [div_div_eq_mul_div, div_one]
  ring

/-- The logarithm is monotone under the factor four in the likelihood argument,
yielding the inequality in CE.8. Given [the displayed inputs and assumptions](hyp:σ,m,hσ,hm,hsat), [the stated mathematical conclusion holds](goal). -/
lemma noiseCost_saturated_le_degree (σ : ℝ) (m : ℕ)
    (hσ : σ ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m)
    (hsat : 1 ≤ σ * Real.sqrt m / 8) :
    1 + noiseCost (noiseResolution σ m) σ ≤
      (m : ℝ) * (1 + Real.log ((m : ℝ) /
        likelihoodLambda (noiseSupport σ m) σ)) := by
  have hs := noiseSupport_saturated_threshold σ m hσ hm hsat
  rw [noiseCost_saturated_eq σ m hσ hm hsat, hs.1, likelihoodLambda]
  simp only [one_pow, div_div_eq_mul_div, div_one]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add_right
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hσp := hσ.1
  apply Real.log_le_log (by positivity)
  nlinarith [sq_nonneg σ, show (0 : ℝ) ≤ m by positivity]


/-- The unsaturated support fixes the likelihood parameter and the scale identity. Given [the displayed inputs and assumptions](hyp:σ,m,hσ,hm,hsat), [the stated mathematical conclusion holds](goal). -/
lemma noiseSupport_unsaturated_identities (σ : ℝ) (m : ℕ)
    (hσ : σ ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m)
    (hsat : σ * Real.sqrt m / 8 < 1) :
    noiseSupport σ m = σ * Real.sqrt m / 8 ∧
    σ^2 * (m : ℝ) = 64 * (noiseSupport σ m)^2 ∧
    likelihoodLambda (noiseSupport σ m) σ = (m : ℝ)/256 := by
  have hb : noiseSupport σ m = σ * Real.sqrt m / 8 := min_eq_right hsat.le
  have hroot := Real.sq_sqrt (show (0 : ℝ) ≤ m by positivity)
  have hσp := hσ.1
  refine ⟨hb, ?_, ?_⟩
  · rw [hb]
    nlinarith [hroot]
  · rw [hb, likelihoodLambda]
    field_simp
    nlinarith [hroot]

/-- CE.5: the intermediate cost is exactly four times the degree. Given [the displayed inputs and assumptions](hyp:σ,m,hσ,hm,hsat,hinter), [the stated mathematical conclusion holds](goal). -/
lemma noiseCost_unsaturated_intermediate_eq (σ : ℝ) (m : ℕ)
    (hσ : σ ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m)
    (hsat : σ * Real.sqrt m / 8 < 1)
    (hinter : σ^4 ≤ noiseResolution σ m) :
    1 + noiseCost (noiseResolution σ m) σ = 4 * (m : ℝ) := by
  have hid := noiseSupport_unsaturated_identities σ m hσ hm hsat
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hσp := hσ.1
  have hbp := (noiseSupport_mem σ m hσ hm).1
  have hhp : 0 < noiseResolution σ m := by unfold noiseResolution; positivity
  have hsmall : noiseResolution σ m < σ := by
    rw [noiseResolution, hid.1]
    have hr : Real.sqrt m < 8 * (m : ℝ)^2 := by
      have hr0 := Real.sqrt_nonneg (m : ℝ)
      have hrs := Real.sq_sqrt hmp.le
      nlinarith [sq_nonneg ((m : ℝ)-1)]
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  rw [noiseCost, if_neg (not_le.mpr hsmall), if_pos hinter]
  have hcube : ((σ / noiseResolution σ m) ^ (2/3 : ℝ))^3 =
      (4 * (m : ℝ))^3 := by
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
    rw [noiseResolution, div_div_eq_mul_div]
    field_simp
    nlinarith [hid.2]
  have heq : (σ / noiseResolution σ m) ^ (2/3 : ℝ) = 4 * (m : ℝ) := by
    exact (pow_left_inj₀ (by positivity) (by positivity) (by norm_num : (3 : ℕ) ≠ 0)).mp hcube
  linarith

/-- CE.6--CE.7 bound the two compact-cost factors throughout unsaturated support. Given [the displayed inputs and assumptions](hyp:σ,M,b,hσ,hM,hb,hb1,hscale,hcompact), [the stated mathematical conclusion holds](goal). -/
lemma noiseCost_compact_support_bound (σ M b : ℝ)
    (hσ : 0 < σ) (hM : 0 < M) (hb : 0 < b) (hb1 : b ≤ 1)
    (hscale : σ^2 * M = 64*b^2) (hcompact : b/M^2 < σ^4) :
    (b/M^2)^(-1/2 : ℝ) * (1 + Real.log (σ^2 / Real.sqrt (b/M^2))) ≤
      4*M*(1 + Real.log 256) := by
  have hfour : σ^4 * M^2 = 4096*b^4 := by
    have hh := congrArg (fun x : ℝ => x^2) hscale
    nlinarith only [hh]
  have hc : b < 4096*b^4 := by
    have hh := (div_lt_iff₀ (show 0 < M^2 by positivity)).mp hcompact
    rwa [hfour] at hh
  have hbmin : (1/16 : ℝ) ≤ b := by
    by_contra hn
    have hh : b ≤ (1/16 : ℝ) := (not_le.mp hn).le
    have hp := pow_le_pow_left₀ hb.le hh 3
    norm_num at hp
    have hmul := mul_le_mul_of_nonneg_left hp hb.le
    nlinarith only [hc, hmul]
  have hhp : 0 < b/M^2 := by positivity
  have hroot : Real.sqrt (b/M^2) = Real.sqrt b / M := by
    rw [Real.sqrt_div hb.le, Real.sqrt_sq hM.le]
  have hmin : 1/(4*M) ≤ Real.sqrt (b/M^2) := by
    have hh := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hbmin
      (show 0 ≤ M^2 by positivity))
    have he : Real.sqrt ((1/16 : ℝ)/M^2) = 1/(4*M) := by
      rw [show (1/16 : ℝ)/M^2 = 1/(4*M)^2 by ring,
        Real.sqrt_div (by norm_num), Real.sqrt_one, Real.sqrt_sq (by positivity)]
    rwa [he] at hh
  have hfactor : (b/M^2)^(-1/2 : ℝ) ≤ 4*M := by
    rw [show (-1/2 : ℝ) = -(1/2 : ℝ) by norm_num,
      Real.rpow_neg hhp.le, ← Real.sqrt_eq_rpow, ← one_div]
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hhp)).mpr
    have hh := (div_le_iff₀ (show 0 < 4*M by positivity)).mp hmin
    nlinarith only [hh]
  have hbpow : b^2 ≤ Real.sqrt b := by
    have hp := pow_le_pow_left₀ hb.le hb1 3
    norm_num at hp
    have hh := mul_le_mul_of_nonneg_left hp hb.le
    have hs := Real.sq_sqrt hb.le
    have hr := Real.sqrt_nonneg b
    nlinarith only [hh, hs, hr, sq_nonneg (b^2 - Real.sqrt b)]
  have harg : σ^2 / Real.sqrt (b/M^2) ≤ 64 := by
    rw [hroot]
    apply (div_le_iff₀ (by positivity : 0 < Real.sqrt b / M)).mpr
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hM).mpr
    nlinarith only [hscale, hbpow]
  have hlog : Real.log (σ^2 / Real.sqrt (b/M^2)) ≤ Real.log 256 :=
    Real.log_le_log (by positivity) (harg.trans (by norm_num))
  have hlogpos : 0 ≤ 1 + Real.log 256 := by
    have hh := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 256)
    linarith
  calc
    _ ≤ (b/M^2)^(-1/2 : ℝ) * (1 + Real.log 256) :=
      mul_le_mul_of_nonneg_left (by linarith only [hlog]) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hfactor hlogpos

/-- CE.5--CE.7 compare both unsaturated cost branches to the likelihood degree exponent. Given [the displayed inputs and assumptions](hyp:σ,m,hσ,hm,hsat), [the stated mathematical conclusion holds](goal). -/
lemma noiseCost_unsaturated_le_degree (σ : ℝ) (m : ℕ)
    (hσ : σ ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m)
    (hsat : σ * Real.sqrt m / 8 < 1) :
    1 + noiseCost (noiseResolution σ m) σ ≤
      4 * (m : ℝ) * (1 + Real.log ((m : ℝ) /
        likelihoodLambda (noiseSupport σ m) σ)) := by
  have hid := noiseSupport_unsaturated_identities σ m hσ hm hsat
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hratio : (m : ℝ) / likelihoodLambda (noiseSupport σ m) σ = 256 := by
    rw [hid.2.2]
    field_simp
  rw [hratio]
  have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 256)
  by_cases hlow : σ ≤ noiseResolution σ m
  · rw [noiseCost, if_pos hlow]
    have hh := mul_nonneg (show 0 ≤ 4*(m : ℝ) by positivity) hlog
    nlinarith only [hm2, hh]
  · by_cases hinter : σ^4 ≤ noiseResolution σ m
    · rw [noiseCost_unsaturated_intermediate_eq σ m hσ hm hsat hinter]
      exact le_mul_of_one_le_right (by positivity) (by linarith)
    · have hb := noiseSupport_mem σ m hσ hm
      have hc := noiseCost_compact_support_bound σ (m : ℝ) (noiseSupport σ m)
        hσ.1 hmp hb.1 hb.2 hid.2.1 (lt_of_not_ge hinter)
      rw [noiseCost, if_neg hlow, if_neg hinter]
      change 1 + ((noiseSupport σ m / (m : ℝ)^2)^(-1/2 : ℝ) *
        (1 + Real.log (σ^2 / Real.sqrt (noiseSupport σ m / (m : ℝ)^2))) - 1) ≤ _
      linarith only [hc]

/-- The optimized one-observation extended information envelope. Given [the displayed inputs and assumptions](hyp:β,σ,m,hβ,hσ,hm), [the stated mathematical conclusion holds](goal). -/
-- @node: lem:cancellation-information-envelope
lemma cancellation_information_envelope (β σ : ℝ) (m : ℕ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hσ : σ ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m) :
    let b := noiseSupport σ m
    let h := noiseResolution σ m
    chiSqExt (Pobs (altLaw classicalLegendreFacts β b m true hβ (noiseSupport_mem σ m hσ hm) hm) σ)
      (Pobs (altLaw classicalLegendreFacts β b m false hβ (noiseSupport_mem σ m hσ hm) hm) σ) ≤
      ENNReal.ofReal ((32/3 : ℝ) * kappa^2 * h^(2*β+1) *
        Real.exp (-(1 + noiseCost h σ)/32)) := by
  let legendre_of_gate : ClassicalLegendreFacts := classicalLegendreFacts
  -- Assemble the degree bound with the support/cost comparisons CE.5--CE.8.
  suffices hcost : 1 + noiseCost (noiseResolution σ m) σ ≤
      4 * (m : ℝ) * (1 +
        Real.log ((m : ℝ)/likelihoodLambda (noiseSupport σ m) σ)) by
    apply (cancellation_information_degree_bound legendre_of_gate β σ m hβ hσ hm).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (by
      have hb := (noiseSupport_mem σ m hσ hm).1.le
      have hh : 0 ≤ noiseResolution σ m := by unfold noiseResolution; positivity
      positivity)
    apply Real.exp_le_exp.mpr
    linarith
  by_cases hsat : 1 ≤ σ * Real.sqrt m / 8
  · have hbound := noiseCost_saturated_le_degree σ m hσ hm hsat
    have hbp := (noiseSupport_mem σ m hσ hm).1
    have hσp := hσ.1
    have hz : 0 < likelihoodLambda (noiseSupport σ m) σ := by
      unfold likelihoodLambda
      positivity
    have hsmall := noiseSupport_likelihoodLambda_le σ m hσ hm
    have hm0 : (0 : ℝ) ≤ m := by positivity
    have hratio : 1 ≤ (m : ℝ) / likelihoodLambda (noiseSupport σ m) σ := by
      rw [le_div_iff₀ hz]
      linarith
    have hB : 0 ≤ (m : ℝ) * (1 +
        Real.log ((m : ℝ) / likelihoodLambda (noiseSupport σ m) σ)) :=
      mul_nonneg hm0 (by linarith [Real.log_nonneg hratio])
    linarith
  · exact noiseCost_unsaturated_le_degree σ m hσ hm (lt_of_not_ge hsat)

end CausalSmith.Stat.RdTruesideNoiseFrontier
