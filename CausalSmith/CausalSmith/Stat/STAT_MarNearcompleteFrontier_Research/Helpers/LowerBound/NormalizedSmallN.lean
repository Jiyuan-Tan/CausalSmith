module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.TParametricFloor
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.Converse.SmallN

/-! # Parametric finite-sample branch of the normalized converse -/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory

-- @node: priorPredictive_pure
/-- The predictive mixture of a point prior is its iid sample law. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
lemma priorPredictive_pure {n d : ℕ} {q : ℝ} (P : ClassLaw d q) :
    priorPredictive n d q (PMF.pure P) = samplePi P.val n := by
  rw [priorPredictive, PMF.toMeasure_pure]
  exact Measure.dirac_bind (by
    intro s hs
    trivial) P

-- @node: priorEventMass_pure
/-- A point prior assigns unit mass to every event containing its support point. Given [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `P`](hyp:P), [the specified input `E`](hyp:E), [the specified input `hE`](hyp:hE), [the stated mathematical conclusion holds](goal). -/
lemma priorEventMass_pure {d : ℕ} {q : ℝ} (P : ClassLaw d q)
    (E : ClassLaw d q → Prop) (hE : E P) :
    priorEventMass d q (PMF.pure P) E = 1 := by
  simp [priorEventMass, PMF.toMeasure_pure, Measure.real_def, hE]

-- @node: normalized_converse_smallN
/-- The one-cell pair proves the normalized-converse certificate below any
fixed positive sample-size threshold. For [a positive tolerance](hyp:hβ), [a positive separation](hyp:ha), [a scale budget valid at every positive integer](hyp:hbudget), [a positive sample size below the threshold](hyp:hn,hN), [a positive dimension](hyp:hd), and [an admissible arrival floor](hyp:hq), [the normalized converse certificate holds](goal). -/
lemma normalized_converse_smallN {n d N : ℕ} {q β a : ℝ}
    (hβ : 0 < β) (ha : 0 < a)
    (hbudget : ∀ m : ℕ, 1 ≤ m →
      0 < a / Real.sqrt m ∧ a / Real.sqrt m ≤ 1 / 4 ∧
        16 * (m : ℝ) * (a / Real.sqrt m) ^ 2 ≤
          Real.log (1 + (2 * β) ^ 2))
    (hn : 1 ≤ n) (hN : n < N) (hd : 1 ≤ d)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    ∃ πminus πplus : PMF (ClassLaw d q),
      Causalean.Stat.tvDist
        (priorPredictive n d q πminus)
        (priorPredictive n d q πplus) ≤ β ∧
      ∃ m0 : ℝ,
        1 - β ≤ priorEventMass d q πminus
          (fun P => tau P.val ≤ m0 -
            (a / Real.sqrt N) * gScale n d q) ∧
        1 - β ≤ priorEventMass d q πplus
          (fun P => m0 + (a / Real.sqrt N) * gScale n d q ≤ tau P.val) := by
  let u := a / Real.sqrt n
  have hu := (hbudget n hn).1
  have huquarter := (hbudget n hn).2.1
  obtain ⟨P₀, P₁, htau₀, htau₁, hac, hchi⟩ :=
    parametric_oneCell_pair hd hq.2 hu huquarter
  have htv : Causalean.Stat.tvDist (samplePi P₀.val n) (samplePi P₁.val n) ≤ β := by
    have htv' := parametric_product_tv_at_tolerance_radius
      (observedLaw P₁.val).toMeasure (observedLaw P₀.val).toMeasure
      hac a (2 * β) (by positivity) hn hbudget hchi
    rw [Causalean.Stat.tvDist_symm]
    simpa [samplePi] using htv'
  have hsep : (a / Real.sqrt N) * gScale n d q ≤ u / 2 := by
    have h := converse_smallN_separation (a / 2) (a / Real.sqrt N) N n d q
      (by positivity) (by positivity) (by ring_nf; exact le_rfl) hn hN hq
    dsimp [u]
    convert h using 1 <;> ring
  refine ⟨PMF.pure P₀, PMF.pure P₁, ?_, 1 / 2 + u / 2, ?_, ?_⟩
  · simpa [priorPredictive_pure] using htv
  · rw [priorEventMass_pure]
    · linarith
    · rw [htau₀]
      linarith
  · rw [priorEventMass_pure]
    · linarith
    · rw [htau₁]
      linarith

end CausalSmith.Stat.MarNearcompleteFrontier
