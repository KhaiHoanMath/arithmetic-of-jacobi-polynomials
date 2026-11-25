/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Applications.JacobianDimension
public import ArithmeticOfJacobiPolynomials.Geometry.AbelianBettiDimension
public import ArithmeticOfJacobiPolynomials.Geometry.AbelianVarietyProduct
public import ArithmeticOfJacobiPolynomials.External

/-!
# Betti dimensions of hyperelliptic Jacobians and their powers

Corollary 6.6: the Jacobian is a representer of
the relative Picard sheaf. Stacks and the proved hyperelliptic genus
formula compute its dimension. The general complex-uniformization input
then supplies the canonical Hodge structure on its singular H₁,
whose dimension and finiteness are proved, also on every positive power.
No Galois-group hypothesis is needed for these dimension assertions.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj

namespace ArithmeticOfJacobiPolynomials

open AbelianBettiHodge ComplexRealization

/-- The singular first homology of any complex hyperelliptic Jacobian
has twice the proved genus as its dimension. -/
theorem jacobianBettiDimension_of_separable
    (hUniform : AbelianBettiHodge.ComplexUniformization)
    {f : ℂ[X]} (hf : f.Separable) (hd : 0 < f.natDegree)
    (B : BigFppfSite.{0}) (hC : B.Contains (Hyperelliptic.projectiveModel f))
    (hℂ : B.Contains (Spec (.of ℂ))) (g : B.obj hC ⟶ B.obj hℂ)
    (hg : B.inclusion.map g = Hyperelliptic.toSpecField f)
    [IsProper (B.inclusion.map g)]
    (hdim : topologicalKrullDim (Hyperelliptic.projectiveModel f) ≤ 1)
    (J : Grp (Over (Spec (.of ℂ))))
    (hJ : Jacobian.IsJacobianOf B hC hℂ g hdim J) :
    ∃ _D : UniformizationData J.X,
      FiniteDimensional ℚ (bettiOne J.X) ∧
      Module.finrank ℚ (bettiOne J.X) = 2 * ((f.natDegree - 1) / 2) := by
  have := hJ.isAbelianVariety
  have : IsCurve ℂ (B.inclusion.map g) := by
    rw [hg]
    exact Hyperelliptic.isCurve_toSpecField (by norm_num) hf hd
  have : IsProjectiveVariety ℂ (B.inclusion.map g) := by
    rw [hg]
    exact Hyperelliptic.isProjectiveVariety_toSpecField (by norm_num) hf hd
  have : Smooth (B.inclusion.map g) := by
    rw [hg]
    exact Hyperelliptic.smooth_toSpecField (by norm_num) hf hd
  let D := Classical.choice (hUniform J.X)
  refine ⟨D, D.finiteDimensional_bettiOne J.X, ?_⟩
  rw [D.finrank_bettiOne_eq_twice_dimension J.X,
    Jacobian.abelianVarietyDimension_eq_genus_of_isAlgClosed B hC ℂ g hJ,
    hg, Hyperelliptic.genus_toSpecField]

/-- A general abelian variety has canonical uniformization data on every
positive power; its first singular homology is finite-dimensional
of the direct-sum dimension. -/
theorem exists_abelianBettiPowerDimensions
    (hUniform : AbelianBettiHodge.ComplexUniformization)
    (A : CSch) [GrpObj A] [IsAbelianVariety ℂ A] :
    ∃ (_DA : UniformizationData A)
      (_D : ∀ h, UniformizationData (GroupScheme.powObj ℂ A (h + 1))),
      ∀ h, FiniteDimensional ℚ (bettiOne (GroupScheme.powObj ℂ A (h + 1))) ∧
        Module.finrank ℚ (bettiOne (GroupScheme.powObj ℂ A (h + 1))) =
          (h + 1) * (2 * Stacks.Groupoids.abelianVarietyDimension A) := by
  let DA := Classical.choice (hUniform A)
  let D (h : ℕ) := Classical.choice (hUniform (GroupScheme.powObj ℂ A (h + 1)))
  refine ⟨DA, D, fun h => ⟨DA.finiteDimensional_bettiPow A D h, ?_⟩⟩
  rw [DA.finrank_bettiPow A D h, DA.finrank_bettiOne_eq_twice_dimension A]

end ArithmeticOfJacobiPolynomials
