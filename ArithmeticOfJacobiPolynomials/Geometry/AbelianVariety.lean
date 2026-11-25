/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.GroupObjectEnd
public import Mathlib.AlgebraicGeometry.Group.Abelian
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVarietyEquivalentDefinitions

/-!
# Abelian varieties over a field

An **abelian variety** over a field `k` is a group object `A` of `Over (Spec k)` whose structure
morphism is a proper, geometrically integral variety ([Stacks, Tag 03RO]). The predicate is
`AlgebraicGeometry.IsAbelianVariety k A` from Stacks, which also proves smoothness
(`AlgebraicGeometry.smooth_of_isAbelianVariety`).

* `AlgebraicGeometry.IsAbelianVariety.isCommMonObj`: the group law is commutative (Mathlib's
  `isCommMonObj_of_isProper_of_geometricallyIntegral`, Stacks Tag 03RP), so the endomorphism ring
  `GrpObjEnd A` (`ArithmeticOfJacobiPolynomials.Algebra.GroupObjectEnd`) applies.

No abelian variety (in particular no Jacobian) is constructed here.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsAbelianVariety

variable {k : Type u} [Field k]

/-- **An abelian variety is commutative.** -/
theorem isCommMonObj {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsAbelianVariety k A] :
    IsCommMonObj A :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A

end AlgebraicGeometry.IsAbelianVariety
