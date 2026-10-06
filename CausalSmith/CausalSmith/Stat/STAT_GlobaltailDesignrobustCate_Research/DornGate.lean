module
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.Witnesses

/-!
# Cited source gate for Dorn's design premises

This standalone proposition records the source-scoped upper-rate transcription.
It is not a theorem of this paper and has no logical consumer in the frozen core.
-/
@[expose] public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

-- @node: lem:dorn-design-premises
/-- Jacob Dorn (2026), *Minimax Rates Under Global Overlap Bounds*,
Assumptions 2 and 3 and Theorem 1, Sections 2–4, author PDF pp. 6–7, 12,
https://jacobdorn.info/files/minimax_rates_under_weak_overlap.pdf.
The source-scoped claim assumes Gaussian conditional outcomes, smooth treated
and control regressions, and uniform local nonconcentration of propensity. It
records the log-free weak-overlap sup-norm upper exponent, with an estimator
chosen without the overlap-tail parameter. -/
def dornDesignPremises : Sort 0 :=
  ∀ (d : ℕ) (β q M σ C L₀ : ℝ),
    1 ≤ d → 0 < β → 3 < q → 0 < M → 0 < σ → 0 < C → 0 < L₀ →
    ∀ 𝔓 : ℝ → Set (CausalSmith.Stat.WeakOverlap.DornSourceLaw d),
      ∃ T : ∀ n : ℕ, (Fin n → CausalSmith.Stat.WeakOverlap.Obs d) →
          (Fin d → ℝ) → ℝ,
        (∀ n x, Measurable (fun ω => T n ω x)) ∧
        ∀ γ : ℝ, 1 < γ →
          CausalSmith.Stat.WeakOverlap.DornA12Family d β q M σ C L₀ γ (𝔓 γ) →
          CausalSmith.Stat.WeakOverlap.DornA3OnOriginalClass (𝔓 γ) →
          ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
            Filter.limsup (fun n : ℕ =>
              ⨆ (z : {z : CausalSmith.Stat.WeakOverlap.DornSourceLaw d // z ∈ 𝔓 γ}),
                (MeasureTheory.Measure.pi (fun _ : Fin n => z.1.1)).real
                  {ω | ENNReal.ofReal
                      (R * (n : ℝ) ^ (-β / (2 * β +
                        CausalSmith.Stat.WeakOverlap.effectiveDimension d γ))) <
                    MeasureTheory.eLpNorm (fun x => T n ω x - z.1.2.1 x) ⊤
                      (CausalSmith.Stat.WeakOverlap.covariateLaw z.1.1)})
              Filter.atTop ≤ ε

end CausalSmith.Stat.GlobalTailDesignRobustCate
