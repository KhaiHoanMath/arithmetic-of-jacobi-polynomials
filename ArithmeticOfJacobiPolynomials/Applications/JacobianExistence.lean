/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.External
public import ArithmeticOfJacobiPolynomials.Geometry.Jacobian.Hyperelliptic

/-!
# General-field Jacobian existence for the explicit hyperelliptic model

The model satisfies the general smooth projective curve assumptions of the cited
Milne Jacobian existence theorem. The specialization needs no rational point.
-/

public section

open CategoryTheory AlgebraicGeometry Polynomial

universe u

namespace ArithmeticOfJacobiPolynomials.Hyperelliptic

variable {K : Type u} [Field K] {f : K[X]}

/-- **Existence of the Jacobian of the hyperelliptic model over any field `K` with `2 ≠ 0`**,
from the cited existence theorem `ArithmeticOfJacobiPolynomials.Jacobian.JacobianExists` ([MilneJV,
Theorem 1.1]); there is no hypothesis that the model has a `K`-rational point. -/
theorem exists_isJacobianOf (hJ : Jacobian.JacobianExists.{u}) (h2 : (2 : K) ≠ 0)
    (hf : f.Separable) (hdeg : 0 < f.natDegree) :
    ∃ G : Grp (Over (Spec (CommRingCat.of K))),
      ∀ (B : BigFppfSite.{u}) (hX : B.Contains (projectiveModel f))
        (hk : B.Contains (Spec (CommRingCat.of K))) (g : B.obj hX ⟶ B.obj hk)
        (hg : B.inclusion.map g = toSpecField f),
        haveI : IsCurve K (toSpecField f) := isCurve_toSpecField h2 hf hdeg
        haveI : IsProper (B.inclusion.map g) := by rw [hg]; exact isProper_toSpecField f
        Nonempty (Jacobian.IsJacobianOf B hX hk g
          (IsCurve.topologicalKrullDim_eq_one (k := K) (f := toSpecField f)).le G) := by
  have := isCurve_toSpecField h2 hf hdeg
  have := geometricallyIrreducible_toSpecField hf hdeg
  have := smooth_toSpecField h2 hf hdeg
  have := isProjectiveVariety_toSpecField h2 hf hdeg
  unfold Jacobian.JacobianExists at hJ
  exact hJ K (toSpecField f)

end ArithmeticOfJacobiPolynomials.Hyperelliptic
