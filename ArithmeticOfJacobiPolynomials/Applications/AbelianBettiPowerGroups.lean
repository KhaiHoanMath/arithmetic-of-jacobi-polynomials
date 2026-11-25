/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Applications.JacobianBettiDimension
public import ArithmeticOfJacobiPolynomials.Geometry.AbelianBettiGroups

/-!
# Selecting geometric Betti data for all powers

The general Milne uniformization input supplies the characterized geometric data.
Finiteness, dimensions and diagonal Hodge/MT transport are then proved together,
without any supplied Hodge-group or dimension assumption. This applies in particular
to the complex hyperelliptic Jacobians constructed in `HyperellipticGeometricCurve`.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace ArithmeticOfJacobiPolynomials

open AbelianBettiHodge ComplexRealization

/-- Every abelian variety has compatible selected power data with the proved
Betti dimensions and transported diagonal Hodge and Mumford–Tate groups. -/
theorem exists_abelianBettiPowerDimensionsAndGroups
    (hUniform : AbelianBettiHodge.ComplexUniformization)
    (A : CSch) [GrpObj A] [IsAbelianVariety ℂ A] :
    ∃ (DA : UniformizationData A)
      (D : ∀ h, UniformizationData (GroupScheme.powObj ℂ A (h + 1))),
      ∀ h, (FiniteDimensional ℚ (bettiOne (GroupScheme.powObj ℂ A (h + 1))) ∧
        Module.finrank ℚ (bettiOne (GroupScheme.powObj ℂ A (h + 1))) =
          (h + 1) * (2 * Stacks.Groupoids.abelianVarietyDimension A)) ∧
        (D h).canonicalHodge.hodgeGroup =
          (DA.canonicalHodge.hodgeGroup.map
            (diagHom ℚ (Fin (h + 1)) (bettiOne A))).map
              (hodgeAutCongr (bettiPowEquiv A DA D h).symm).toMonoidHom ∧
        (D h).canonicalHodge.mumfordTateGroup =
          (DA.canonicalHodge.mumfordTateGroup.map
            (diagHom ℚ (Fin (h + 1)) (bettiOne A))).map
              (hodgeAutCongr (bettiPowEquiv A DA D h).symm).toMonoidHom := by
  obtain ⟨DA, D, hd⟩ := exists_abelianBettiPowerDimensions hUniform A
  exact ⟨DA, D, fun h => ⟨hd h, DA.hodgeGroup_bettiPow A D h,
    DA.mumfordTateGroup_bettiPow A D h⟩⟩

end ArithmeticOfJacobiPolynomials
