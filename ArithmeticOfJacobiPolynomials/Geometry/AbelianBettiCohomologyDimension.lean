/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.AbelianBettiCohomology
public import ArithmeticOfJacobiPolynomials.Geometry.AbelianBettiDimension

/-!
# Dimension of first Betti cohomology

The universal coefficient equivalence identifies singular cohomology
with the dual of singular homology. Mathlib proves that finite-dimensional
duals have the same dimension. Combining this with the proved period-space
dimension gives `dim H¹(A(ℂ), ℚ) = 2 dim A`, also for all positive powers.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace ArithmeticOfJacobiPolynomials.AbelianBettiHodge

open AbelianBettiCohomology ComplexRealization

variable (A : CSch) [GrpObj A]

/-- First singular cohomology is finite-dimensional whenever the
characterized uniformization provides the finite period space. -/
theorem UniformizationData.finiteDimensional_bettiCohomologyOne
    [LocallyOfFiniteType A.hom] (D : UniformizationData A) :
    FiniteDimensional ℚ (bettiCohomology A 1) := by
  have := D.finiteDimensional_bettiOne A
  exact Module.Finite.equiv (bettiUC A 1).symm

/-- The dimension of `H¹(A(ℂ), ℚ)` equals twice the geometric dimension. -/
theorem UniformizationData.finrank_bettiCohomologyOne_eq_twice_dimension
    [IsAbelianVariety ℂ A] (D : UniformizationData A) :
    Module.finrank ℚ (bettiCohomology A 1) =
      2 * Stacks.Groupoids.abelianVarietyDimension A := by
  rw [(bettiUC A 1).finrank_eq, Subspace.dual_finrank_eq]
  exact D.finrank_bettiOne_eq_twice_dimension A

/-- The first cohomology of every positive power is finite-dimensional. -/
theorem UniformizationData.finiteDimensional_bettiCohomologyPow
    [LocallyOfFiniteType A.hom] (DA : UniformizationData A)
    (D : ∀ h, UniformizationData (GroupScheme.powObj ℂ A (h + 1))) (h : ℕ) :
    FiniteDimensional ℚ (bettiCohomology (GroupScheme.powObj ℂ A (h + 1)) 1) := by
  have := DA.finiteDimensional_bettiPow A D h
  exact Module.Finite.equiv (bettiUC (GroupScheme.powObj ℂ A (h + 1)) 1).symm

/-- The universal coefficient equivalence and the projection comparison
compute `dim H¹(A^(h+1)(ℂ), ℚ)` from the dimension of the original variety. -/
theorem UniformizationData.finrank_bettiCohomologyPow
    [IsAbelianVariety ℂ A] (DA : UniformizationData A)
    (D : ∀ h, UniformizationData (GroupScheme.powObj ℂ A (h + 1))) (h : ℕ) :
    Module.finrank ℚ (bettiCohomology (GroupScheme.powObj ℂ A (h + 1)) 1) =
      (h + 1) * (2 * Stacks.Groupoids.abelianVarietyDimension A) := by
  rw [(bettiUC (GroupScheme.powObj ℂ A (h + 1)) 1).finrank_eq,
    Subspace.dual_finrank_eq]
  rw [DA.finrank_bettiPow A D h, DA.finrank_bettiOne_eq_twice_dimension A]

end ArithmeticOfJacobiPolynomials.AbelianBettiHodge
