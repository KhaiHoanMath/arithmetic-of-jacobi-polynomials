/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.Jacobian.Hyperelliptic

/-!
# General hyperelliptic models for the literature statements

The presentation below applies to any smooth projective curve with a nonempty open
chart of equation `y² = f(x)`. It does not prescribe a particular compactification.
The projective model constructed for the manuscript satisfies this presentation.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial

universe u

namespace ArithmeticOfJacobiPolynomials

namespace Zarhin

/-- A general smooth projective model of the affine equation `y² = f(x)`.
The open immersion identifies the affine equation with an open subscheme. -/
structure HyperellipticModel {k : Type u} [Field k] (f : k[X])
    (C : Over (Spec (CommRingCat.of k))) : Prop where
  isCurve : IsCurve k C.hom
  smooth : Smooth C.hom
  projective : IsProjectiveVariety k C.hom
  geometricallyIrreducible : GeometricallyIrreducible C.hom
  affineChart : ∃ ι : Spec (CommRingCat.of (HyperellipticCoordRing f)) ⟶ C.left,
    IsOpenImmersion ι ∧
      ι ≫ C.hom = Spec.map (CommRingCat.ofHom (algebraMap k (HyperellipticCoordRing f)))

/-- The explicit two-chart projective curve has the general presentation used by Zarhin. -/
theorem hyperellipticModel_projectiveModel {k : Type u} [Field k] {f : k[X]}
    (h2 : (2 : k) ≠ 0) (hf : f.Separable) (hd : 0 < f.natDegree) :
    HyperellipticModel f (Over.mk (Hyperelliptic.toSpecField f)) where
  isCurve := Hyperelliptic.isCurve_toSpecField h2 hf hd
  smooth := Hyperelliptic.smooth_toSpecField h2 hf hd
  projective := Hyperelliptic.isProjectiveVariety_toSpecField h2 hf hd
  geometricallyIrreducible := Hyperelliptic.geometricallyIrreducible_toSpecField hf hd
  affineChart := ⟨Hyperelliptic.affineChart f, inferInstance,
    Hyperelliptic.chart_toSpecField (Hyperelliptic.chartData_finite f)⟩

end Zarhin

end ArithmeticOfJacobiPolynomials
