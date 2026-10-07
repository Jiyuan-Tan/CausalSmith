module
public import Causalean.Mathlib.Geometry.Manifold.EmbeddedNormalGeometry.NormalBundle
public import Causalean.Mathlib.Geometry.Manifold.EmbeddedNormalGeometry.ShapeOperator
public import Causalean.Mathlib.Geometry.Manifold.EmbeddedNormalGeometry.Tangent

/-!
# Tangent spaces, second fundamental form and normal fibers of an embedded manifold

Let f be a C² embedding of a finite-dimensional manifold M, possibly with boundary or corners,
into a finite-dimensional Euclidean space. The tangent space at x is the range of the
differential of f and the normal space is its orthogonal complement; the two are complementary
and the tangent space has the dimension of the model space. The second fundamental form is the
symmetric bilinear form on the tangent space, with values in the normal space, given in any chart
by the normal component of the Hessian of the parametrization, and it is the unique form with
this property. Each normal vector determines a self-adjoint shape operator on the tangent space.
The normal fibers carry their Lebesgue measures measurably in the base point, so integrals over
the bundle of normal disks are iterated integrals.

## Contents

* `EmbeddedNormalGeometry.Tangent` — `tangentSpace`, `normalSpace`, `tangent_normal_isCompl`,
  `tangentSpace_finrank`, continuity of the two orthogonal projections.
* `EmbeddedNormalGeometry.ShapeOperator` — `secondFundamentalForm` with
  `secondFundamentalForm_symmetric`, `secondFundamentalForm_chart` and
  `secondFundamentalForm_unique`; `embeddingShapeOperator` and its self-adjointness; the
  determinant `tubeDeterminant` of the identity minus a scaled shape operator.
* `EmbeddedNormalGeometry.NormalBundle` — closed normal disk bundles, the fiber volume kernels
  `normalFiberVolumeKernel` and `normalDiskVolumeKernel`, and the iterated integration formula
  `lintegral_normalDiskReferenceMeasure`.

This file only gathers the modules above.
-/
public section
