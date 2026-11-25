/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.AbelianBettiDimension
public import ArithmeticOfJacobiPolynomials.Algebra.HodgeStructureIso

/-!
# Diagonal Hodge and Mumford–Tate groups on Betti powers

The scheme projections identify the first singular homology of
`A^(h+1)` with the direct sum of `h+1` copies of `H₁(A(ℂ), ℚ)`. This comparison
intertwines the canonical complex structures. Thus the abstract diagonal group
formulas apply to these Betti spaces.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace ArithmeticOfJacobiPolynomials.AbelianBettiHodge

open ArithmeticOfJacobiPolynomials.ComplexRealization ArithmeticOfJacobiPolynomials.GroupScheme

variable (A : CSch) [GrpObj A] (DA : UniformizationData A)
  (D : ∀ h, UniformizationData (powObj ℂ A (h + 1)))

/-- The positive-power comparison carries exactly the rational tensor Hodge classes. -/
theorem UniformizationData.hodgeClasses_bettiPow_iff (h m n : ℕ)
    (t : TensorSpace ℚ (bettiOne (powObj ℂ A (h + 1))) m n) :
    hodgeTensorEquiv (bettiPowEquiv A DA D h) m n t ∈
        (DA.canonicalHodge.pi (Fin (h + 1))).hodgeClasses m n ↔
      t ∈ (D h).canonicalHodge.hodgeClasses m n :=
  HodgeStructureNegOne.hodgeTensorEquiv_mem_iff (D h).canonicalHodge
    (DA.canonicalHodge.pi (Fin (h + 1))) (bettiPowEquiv A DA D h)
    (realEquiv_bettiPowEquiv_J A DA D h)

/-- The Hodge group of the positive power is the transported diagonal group. -/
theorem UniformizationData.hodgeGroup_bettiPow [LocallyOfFiniteType A.hom] (h : ℕ) :
    (D h).canonicalHodge.hodgeGroup =
      (DA.canonicalHodge.hodgeGroup.map
        (ArithmeticOfJacobiPolynomials.diagHom ℚ (Fin (h + 1)) (bettiOne A))).map
          (hodgeAutCongr (bettiPowEquiv A DA D h).symm).toMonoidHom := by
  have := DA.finiteDimensional_bettiOne A
  have hJ := HodgeStructureNegOne.inverse_commutes_J (D h).canonicalHodge
    (DA.canonicalHodge.pi (Fin (h + 1))) (bettiPowEquiv A DA D h)
    (realEquiv_bettiPowEquiv_J A DA D h)
  rw [HodgeStructureNegOne.hodgeGroup_eq_map
    (DA.canonicalHodge.pi (Fin (h + 1))) (D h).canonicalHodge
    (bettiPowEquiv A DA D h).symm hJ, DA.canonicalHodge.hodgeGroup_pi]

/-- The Mumford–Tate group of the positive power has the same diagonal transport. -/
theorem UniformizationData.mumfordTateGroup_bettiPow [LocallyOfFiniteType A.hom] (h : ℕ) :
    (D h).canonicalHodge.mumfordTateGroup =
      (DA.canonicalHodge.mumfordTateGroup.map
        (ArithmeticOfJacobiPolynomials.diagHom ℚ (Fin (h + 1)) (bettiOne A))).map
          (hodgeAutCongr (bettiPowEquiv A DA D h).symm).toMonoidHom := by
  have := DA.finiteDimensional_bettiOne A
  have hJ := HodgeStructureNegOne.inverse_commutes_J (D h).canonicalHodge
    (DA.canonicalHodge.pi (Fin (h + 1))) (bettiPowEquiv A DA D h)
    (realEquiv_bettiPowEquiv_J A DA D h)
  rw [HodgeStructureNegOne.mumfordTateGroup_eq_map
    (DA.canonicalHodge.pi (Fin (h + 1))) (D h).canonicalHodge
    (bettiPowEquiv A DA D h).symm hJ, DA.canonicalHodge.mumfordTateGroup_pi]

end ArithmeticOfJacobiPolynomials.AbelianBettiHodge
