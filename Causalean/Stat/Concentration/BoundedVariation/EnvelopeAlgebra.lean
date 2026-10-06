module
public import Causalean.Stat.Concentration.BoundedVariation.Variation

/-!
# Bounded-variation envelope under subtraction

The real total variation and supremum-plus-variation envelope of a difference
are bounded by the corresponding sums for its two paths. These facts allow a
product-law copy to be used in the centered-process argument.
-/

public section

namespace Causalean.Stat.Concentration.BoundedVariation

/-- [The extended total variation of the difference of two continuous
paths is at most the sum of their extended total variations](goal).

In particular differences of bounded-variation paths have bounded variation.
-/
theorem eVariationOn_path_sub_le (f g : Path) :
    eVariationOn (f - g) Set.univ ≤
      eVariationOn f Set.univ + eVariationOn g Set.univ := by
    apply iSup_le
    rintro ⟨n, ⟨u, hu, hus⟩⟩
    calc
      (∑ i ∈ Finset.range n,
          edist ((f - g) (u (i + 1))) ((f - g) (u i))) ≤
          (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) +
          (∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i))) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_le_sum
            intro i hi
            simpa [ContinuousMap.sub_apply, vsub_eq_sub] using
              (edist_vsub_vsub_le (f (u (i + 1))) (g (u (i + 1)))
                (f (u i)) (g (u i)))
      _ ≤ eVariationOn f Set.univ + eVariationOn g Set.univ :=
        add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)

/-- If [the path f has finite total variation](hyp:hf) and [so does
the path g](hyp:hg), then [the total variation of f − g is at most the sum
of the total variations of f and g](goal).
-/
theorem pathTV_sub_le (f g : Path)
    (hf : eVariationOn f Set.univ < ⊤)
    (hg : eVariationOn g Set.univ < ⊤) :
    pathTV (f - g) ≤ pathTV f + pathTV g := by
  have he := eVariationOn_path_sub_le f g
  simpa [pathTV, ENNReal.toReal_add (ne_of_lt hf) (ne_of_lt hg)] using
    (ENNReal.toReal_mono (ne_of_lt (ENNReal.add_lt_top.mpr ⟨hf, hg⟩)) he)

/-- If [the path f has finite total variation](hyp:hf) and [so does
the path g](hyp:hg), then [the supremum-plus-variation size of f − g is at
most the sum of the sizes of f and g](goal).
-/
theorem pathSize_sub_le (f g : Path)
    (hf : eVariationOn f Set.univ < ⊤)
    (hg : eVariationOn g Set.univ < ⊤) :
    pathSize (f - g) ≤ pathSize f + pathSize g := by
  dsimp [pathSize]
  have hnorm : ‖f - g‖ ≤ ‖f‖ + ‖g‖ := norm_sub_le f g
  have htv := pathTV_sub_le f g hf hg
  linarith

end Causalean.Stat.Concentration.BoundedVariation
