module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionCollarGeometry
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionFaceGluing
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionSampleJets

/-!
# Quantitative jets on the closed exterior side of a face collar

The open exterior estimates pass to the face and the other coordinate edges
through continuous within-collar jets. Both conclusions concern derivatives
within the full collar, so they can be used directly in collar bounds.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

private theorem leftFaceReflection_withinJet_eq_ambient_on_open
    (d m j : ℕ) (i : Fin d) (a : Fin (m + 1) → ℝ)
    (u : (Fin d → ℝ) → ℝ) (hu : ContDiffOn ℝ m u (cube d))
    (hj : j ≤ m) (x : Fin d → ℝ)
    (hx : x ∈ leftOpenCubeCollar d m i) :
    iteratedFDerivWithin ℝ j (leftFaceReflection d m i a u)
      (leftCubeCollar d m i) x =
    iteratedFDeriv ℝ j (leftFaceReflection d m i a u) x := by
  have hopen : IsOpen (leftOpenCubeCollar d m i) := by
    have heq : leftOpenCubeCollar d m i = Set.univ.pi (fun k : Fin d =>
        if k = i then Set.Ioo (-1 - (1 : ℝ) / ((m : ℝ) + 1)) (-1)
        else Set.Ioo (-1 : ℝ) 1) := by
      ext z
      simp only [leftOpenCubeCollar, Set.mem_ofPred_eq, Set.mem_univ_pi]
      constructor <;> intro h k <;> by_cases hk : k = i <;>
        simpa [hk] using h k
    rw [heq]
    apply isOpen_set_pi Set.finite_univ
    intro k hk
    split_ifs <;> exact isOpen_Ioo
  have hclosed : x ∈ leftCubeCollar d m i := by
    have h : x ∈ closure (leftOpenCubeCollar d m i) := subset_closure hx
    rw [closure_leftOpenCubeCollar] at h
    exact h.1
  have hreg : ContDiffAt ℝ j (leftFaceReflection d m i a u) x :=
    ((leftFaceReflection_contDiffOn_openCollar d m i a u hu).contDiffAt
      (hopen.mem_nhds hx)).of_le (by exact_mod_cast hj)
  exact iteratedFDerivWithin_eq_iteratedFDeriv
    (uniqueDiffOn_leftCubeCollar d m i) hreg hclosed

/-- If [the reflection weights a satisfy the moment conditions
Σ_q a_q·(−(q + 1))^k = 1 for every k ≤ m](hyp:ha), then [there is a positive
constant C such that, for every response u in the intrinsic Hölder ball of order
m, exponent s and radius L ≥ 0 on the normalized cube, the within-collar Fréchet
derivatives of the one-face reflection of u of every order at most m have
operator norm at most C·L at every point of the closed exterior slab](goal). -/
theorem exists_leftFaceReflection_closedExterior_jet_bound
    (d m : ℕ) (s : ℝ) (i : Fin d) (a : Fin (m + 1) → ℝ)
    (ha : ∀ k : Fin (m + 1),
      (∑ q : Fin (m + 1),
        a q * (-((q.val : ℝ) + 1)) ^ (k.val : ℕ)) = 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (L : ℝ), 0 ≤ L →
        CubeHolderBall d m s L u →
        ∀ j ≤ m, ∀ x ∈ leftClosedExteriorCollar d m i,
          ‖iteratedFDerivWithin ℝ j (leftFaceReflection d m i a u)
            (leftCubeCollar d m i) x‖ ≤ C * L := by
  obtain ⟨C, hC, hbound⟩ := exists_leftFaceReflection_jet_bound d m s i a
  refine ⟨C, hC, ?_⟩
  intro u L hL hu j hj x hx
  have hreg := leftFaceReflection_contDiffOn_collar d m i a ha u hu.regularity
  have hcont : ContinuousOn
      (fun z => ‖iteratedFDerivWithin ℝ j (leftFaceReflection d m i a u)
        (leftCubeCollar d m i) z‖) (leftCubeCollar d m i) :=
    ((hreg.continuousOn_iteratedFDerivWithin
      (by exact_mod_cast hj) (uniqueDiffOn_leftCubeCollar d m i)).norm)
  have hle := le_on_closure
    (s := leftOpenCubeCollar d m i)
    (f := fun z => ‖iteratedFDerivWithin ℝ j (leftFaceReflection d m i a u)
      (leftCubeCollar d m i) z‖)
    (g := fun _ => C * L)
    (by
      intro z hz
      rw [leftFaceReflection_withinJet_eq_ambient_on_open d m j i a u
        hu.regularity hj z hz]
      exact hbound u L hL hu j hj z hz)
    (by
      rw [closure_leftOpenCubeCollar]
      exact hcont.mono (fun z hz => hz.1))
    continuousOn_const
  exact hle (by rwa [closure_leftOpenCubeCollar])

/-- If [s > 0](hyp:hs) and [the reflection weights a satisfy the moment
conditions Σ_q a_q·(−(q + 1))^k = 1 for every k ≤ m](hyp:ha), then [there is a
positive constant C such that, for every response u in the intrinsic Hölder ball
of order m, exponent s and radius L ≥ 0 on the normalized cube, the order-m
within-collar Fréchet derivative of the one-face reflection of u is s-Hölder
with coefficient C·L between any two points of the closed exterior slab](goal). -/
theorem exists_leftFaceReflection_closedExterior_top_modulus
    (d m : ℕ) (s : ℝ) (hs : 0 < s)
    (i : Fin d) (a : Fin (m + 1) → ℝ)
    (ha : ∀ k : Fin (m + 1),
      (∑ q : Fin (m + 1),
        a q * (-((q.val : ℝ) + 1)) ^ (k.val : ℕ)) = 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (L : ℝ), 0 ≤ L →
        CubeHolderBall d m s L u →
        ∀ x ∈ leftClosedExteriorCollar d m i,
          ∀ y ∈ leftClosedExteriorCollar d m i,
            ‖iteratedFDerivWithin ℝ m (leftFaceReflection d m i a u)
                (leftCubeCollar d m i) x -
              iteratedFDerivWithin ℝ m (leftFaceReflection d m i a u)
                (leftCubeCollar d m i) y‖
              ≤ C * L * ‖x - y‖ ^ s := by
  obtain ⟨C, hC, hbound⟩ := exists_leftFaceReflection_top_modulus d m s hs i a
  refine ⟨C, hC, ?_⟩
  intro u L hL hu
  let J := iteratedFDerivWithin ℝ m (leftFaceReflection d m i a u)
    (leftCubeCollar d m i)
  have hJ : ContinuousOn J (leftClosedExteriorCollar d m i) := by
    have hreg := leftFaceReflection_contDiffOn_collar d m i a ha u hu.regularity
    exact (hreg.continuousOn_iteratedFDerivWithin
      (by exact_mod_cast (le_refl m)) (uniqueDiffOn_leftCubeCollar d m i)).mono
      (fun z hz => hz.1)
  have hpow (z : Fin d → ℝ) : Continuous (fun w : Fin d → ℝ => ‖w - z‖ ^ s) :=
    ((continuous_id.sub continuous_const).norm).rpow_const
      (fun _ => Or.inr hs.le)
  have hfirst (z : Fin d → ℝ) (hz : z ∈ leftOpenCubeCollar d m i) :
      ∀ x ∈ leftClosedExteriorCollar d m i,
        ‖J x - J z‖ ≤ C * L * ‖x - z‖ ^ s := by
    have hz' : z ∈ leftClosedExteriorCollar d m i := by
      rw [← closure_leftOpenCubeCollar]
      exact subset_closure hz
    intro x hx
    have h := le_on_closure
      (s := leftOpenCubeCollar d m i)
      (f := fun w => ‖J w - J z‖)
      (g := fun w => C * L * ‖w - z‖ ^ s)
      (by
        intro w hw
        change ‖iteratedFDerivWithin ℝ m (leftFaceReflection d m i a u)
          (leftCubeCollar d m i) w -
          iteratedFDerivWithin ℝ m (leftFaceReflection d m i a u)
            (leftCubeCollar d m i) z‖ ≤ _
        rw [leftFaceReflection_withinJet_eq_ambient_on_open d m m i a u
          hu.regularity le_rfl w hw,
          leftFaceReflection_withinJet_eq_ambient_on_open d m m i a u
          hu.regularity le_rfl z hz]
        exact hbound u L hL hu w hw z hz)
      (by
        rw [closure_leftOpenCubeCollar]
        exact (hJ.sub continuousOn_const).norm)
      (by
        rw [closure_leftOpenCubeCollar]
        exact continuousOn_const.mul (hpow z).continuousOn)
    exact h (by rwa [closure_leftOpenCubeCollar])
  intro x hx y hy
  have h := le_on_closure
    (s := leftOpenCubeCollar d m i)
    (f := fun z => ‖J x - J z‖)
    (g := fun z => C * L * ‖x - z‖ ^ s)
    (by intro z hz; exact hfirst z hz x hx)
    (by
      rw [closure_leftOpenCubeCollar]
      exact (continuousOn_const.sub hJ).norm)
    (by
      rw [closure_leftOpenCubeCollar]
      exact continuousOn_const.mul
        (((continuous_const.sub continuous_id).norm).rpow_const
          (fun _ => Or.inr hs.le)).continuousOn)
  exact h (by rwa [closure_leftOpenCubeCollar])

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
