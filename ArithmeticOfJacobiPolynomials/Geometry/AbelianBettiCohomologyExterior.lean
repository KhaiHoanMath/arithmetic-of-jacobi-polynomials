/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.AbelianHodgeClasses
public import ArithmeticOfJacobiPolynomials.Geometry.AbelianBettiCohomologyDimension
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Higher Betti cohomology dimensions

A comparison normalized by the cochain cup product identifies singular
cohomology with the exterior power of its first cohomology. Mathlib computes
the exterior-power dimension. The first-cohomology dimension is already proved
from the period comparison.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace ArithmeticOfJacobiPolynomials.AbelianBettiHodge

open AbelianBettiCohomology AbelianHodgeClasses

variable (A : CSch) [GrpObj A]

/-- Singular cohomology in every degree is finite-dimensional,
relative to its geometrically normalized cup comparison. -/
theorem UniformizationData.finiteDimensional_bettiCohomology
    [LocallyOfFiniteType A.hom] (D : UniformizationData A) {r : ℕ}
    (c : CupComparison A r) : FiniteDimensional ℚ (bettiCohomology A r) := by
  have := D.finiteDimensional_bettiCohomologyOne A
  exact Module.Finite.equiv c.toEquiv

/-- `dim Hʳ(A(ℂ), ℚ) = choose(2 dim A, r)` for the cohomology. -/
theorem UniformizationData.finrank_bettiCohomology
    [IsAbelianVariety ℂ A] (D : UniformizationData A) {r : ℕ}
    (c : CupComparison A r) :
    Module.finrank ℚ (bettiCohomology A r) =
      (2 * Stacks.Groupoids.abelianVarietyDimension A).choose r := by
  have := D.finiteDimensional_bettiCohomologyOne A
  rw [← c.toEquiv.finrank_eq, exteriorPower.finrank_eq]
  rw [D.finrank_bettiCohomologyOne_eq_twice_dimension A]

/-- Higher cohomology of the positive power has the binomial dimension
computed from the original variety. -/
theorem UniformizationData.finrank_bettiCohomologyPower
    [IsAbelianVariety ℂ A] (DA : UniformizationData A)
    (D : ∀ h, UniformizationData (GroupScheme.powObj ℂ A (h + 1))) (h r : ℕ)
    (c : CupComparison (GroupScheme.powObj ℂ A (h + 1)) r) :
    Module.finrank ℚ (bettiCohomology (GroupScheme.powObj ℂ A (h + 1)) r) =
      ((h + 1) * (2 * Stacks.Groupoids.abelianVarietyDimension A)).choose r := by
  have := DA.finiteDimensional_bettiCohomologyPow A D h
  rw [← c.toEquiv.finrank_eq, exteriorPower.finrank_eq]
  rw [DA.finrank_bettiCohomologyPow A D h]

end ArithmeticOfJacobiPolynomials.AbelianBettiHodge
