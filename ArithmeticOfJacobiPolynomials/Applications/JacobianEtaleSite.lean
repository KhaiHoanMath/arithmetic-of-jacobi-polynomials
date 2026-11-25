/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.AbelianEtaleCohomology
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConstantComplexModelsTransport

/-!
# Library witnesses for the étale-site conditions of Corollary 6.6

The site conditions used to state the cycle-class conclusion (Corollary 6.6)
are available from the library's sheafification and pullback adjunctions.
This file packages those proofs.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ArithmeticOfJacobiPolynomials

/-- Stacks sheafification and Mathlib's sheaf pullback adjunction discharge all
site conditions used by the manuscript's cycle-class target. -/
theorem jacobianEllAdicSite (B : BigEtaleSite.{0}) (ℓ : ℕ) :
    AbelianEtale.EllAdicSite B ℓ := {
  hasWeakSheafify := fun n T =>
    (Stacks.ConstantSheaf.hasSheafifyModuleCatOfSmall.{1, 0, 1, 0}
      (SmallEtale.topology B T.1 T.property) (ZMod (ℓ ^ (n + 1)))).isRightAdjoint
  hasWeakSheafifyOver := fun n T V =>
    (Stacks.ConstantSheaf.hasSheafifyModuleCatOfSmall.{1, 0, 1, 0}
      ((SmallEtale.topology B T.1 T.property).over V)
      (ZMod (ℓ ^ (n + 1)))).isRightAdjoint
  isRightAdjoint := by
    intro n S T f
    have := (Stacks.ConstantSheaf.hasSheafifyModuleCatOfSmall.{1, 0, 1, 0}
      (SmallEtale.topology B T.1 T.property) (ZMod (ℓ ^ (n + 1)))).isRightAdjoint
    infer_instance
}

end ArithmeticOfJacobiPolynomials
