/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.External
public import ArithmeticOfJacobiPolynomials.Geometry.AbelianBettiCohomologyExterior
public import ArithmeticOfJacobiPolynomials.Geometry.AbelianVarietyProduct

/-!
# Torus cohomology comparisons for abelian varieties

The general complex-uniformization input identifies the analytic space with a
real torus. Milne's general theorem on all real tori supplies the cup-normalized
comparison. Its use here selects the geometric data and proves the
cohomology dimensions, including on all positive powers.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace ArithmeticOfJacobiPolynomials

open AbelianBettiHodge AbelianBettiCohomology AbelianHodgeClasses ComplexRealization

/-- The theorem on arbitrary real tori supplies the geometrically normalized
comparison for every complex abelian variety with uniformization data. -/
theorem exists_bettiCupComparison (hCup : TorusBettiCupProduct)
    (A : CSch) [GrpObj A] (D : UniformizationData A) (r : ℕ) :
    Nonempty (CupComparison A r) := by
  obtain ⟨n, hn⟩ := D.torusTopology
  obtain ⟨e, he⟩ := hCup (space A) n hn r
  exact ⟨⟨e, he⟩⟩

/-- Select uniformization and cup comparison data, then compute the
finite dimension of singular cohomology in every degree. -/
theorem exists_abelianBettiCohomologyDimensions
    (hUniform : AbelianBettiHodge.ComplexUniformization) (hCup : TorusBettiCupProduct)
    (A : CSch) [GrpObj A] [IsAbelianVariety ℂ A] :
    ∃ (_D : UniformizationData A) (_c : ∀ r, CupComparison A r), ∀ r,
      FiniteDimensional ℚ (bettiCohomology A r) ∧
      Module.finrank ℚ (bettiCohomology A r) =
        (2 * Stacks.Groupoids.abelianVarietyDimension A).choose r := by
  let D := Classical.choice (hUniform A)
  let c (r : ℕ) := Classical.choice (exists_bettiCupComparison hCup A D r)
  exact ⟨D, c, fun r => ⟨D.finiteDimensional_bettiCohomology A (c r),
    D.finrank_bettiCohomology A (c r)⟩⟩

/-- Every positive power has its cup-normalized comparison in all
degrees, with the binomial cohomology dimension of that power. -/
theorem exists_abelianBettiPowerCohomologyDimensions
    (hUniform : AbelianBettiHodge.ComplexUniformization) (hCup : TorusBettiCupProduct)
    (A : CSch) [GrpObj A] [IsAbelianVariety ℂ A] :
    ∃ (_DA : UniformizationData A)
      (_D : ∀ h, UniformizationData (GroupScheme.powObj ℂ A (h + 1)))
      (_c : ∀ h r, CupComparison (GroupScheme.powObj ℂ A (h + 1)) r), ∀ h r,
      FiniteDimensional ℚ (bettiCohomology (GroupScheme.powObj ℂ A (h + 1)) r) ∧
      Module.finrank ℚ (bettiCohomology (GroupScheme.powObj ℂ A (h + 1)) r) =
        ((h + 1) * (2 * Stacks.Groupoids.abelianVarietyDimension A)).choose r := by
  let DA := Classical.choice (hUniform A)
  let D (h : ℕ) := Classical.choice (hUniform (GroupScheme.powObj ℂ A (h + 1)))
  let c (h r : ℕ) := Classical.choice
    (exists_bettiCupComparison hCup (GroupScheme.powObj ℂ A (h + 1)) (D h) r)
  exact ⟨DA, D, c, fun h r =>
    ⟨(D h).finiteDimensional_bettiCohomology (GroupScheme.powObj ℂ A (h + 1)) (c h r),
      DA.finrank_bettiCohomologyPower A D h r (c h r)⟩⟩

end ArithmeticOfJacobiPolynomials
