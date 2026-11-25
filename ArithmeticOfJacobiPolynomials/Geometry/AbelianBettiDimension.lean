/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.AbelianBettiHodge
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.RelativeEmbeddingDimensionForms
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.ConnectedRelativeDimension

/-!
# Dimension of the singular first homology

For Corollary 6.6, the finite-dimensionality of
`H₁(A(ℂ), ℚ)` is proved from the characterized period isomorphism. Stacks computes the dimension
of the tangent space of a smooth variety (0CBK); transporting its residue-field scalars to
`ℂ` and then restricting to `ℝ` yields `dimℚ H₁ = 2 dim A`.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace ArithmeticOfJacobiPolynomials.AbelianBettiHodge

attribute [local instance] residueSMulComm residueSMulComm'
attribute [local instance] Stacks.SmoothAtJacobian.relativeDifferentialStalkModule

private abbrev residueAlgebra {X : Scheme} (x : X) :
    Algebra (X.presheaf.stalk x) (X.residueField x) :=
  (X.residue x).hom.toAlgebra

private abbrev residueTower {X : Scheme} (x : X) :
    IsScalarTower (X.presheaf.stalk x) (X.residueField x) (X.residueField x) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] residueAlgebra residueTower

/-- The locally finite type condition makes the Stacks tangent space finite-dimensional:
it is the dual of the finite relative cotangent space. -/
theorem finiteDimensional_dottedTangentArrow {X S : Scheme} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) :
    FiniteDimensional (X.residueField x) (DottedTangentArrow f x) := by
  have : FiniteDimensional (X.residueField x)
      (X.residueField x ⊗[X.presheaf.stalk x]
        Stacks.SmoothAtJacobian.relativeDifferentialStalk f x) :=
    finiteDimensional_relativeCotangentSpace f x
  let e := (tangentSpaceEquivCotangentSpace f x).trans
    (LinearMap.liftBaseChangeEquiv (R := X.presheaf.stalk x) (X.residueField x)
      (M := Stacks.SmoothAtJacobian.relativeDifferentialStalk f x)
      (N := X.residueField x))
  exact Module.Finite.equiv e.symm

variable (A : CSch)

/-- A basis for the tangent space, with scalars transported by the canonical
identification `κ(σ) ≃ ℂ`. -/
def tangentBasis [LocallyOfFiniteType A.hom] (σ :
  ArithmeticOfJacobiPolynomials.ComplexRealization.Points A) :
    Module.Basis (Fin (Module.finrank (A.left.residueField (secPt σ))
      (DottedTangentArrow A.hom (secPt σ)))) ℂ (TangentAt A σ) := by
  letI := finiteDimensional_dottedTangentArrow A.hom (secPt σ)
  letI : Module ℂ (DottedTangentArrow A.hom (secPt σ)) :=
    Module.compHom _ (resEquiv σ).symm.toRingHom
  exact (Module.finBasis (A.left.residueField (secPt σ))
    (DottedTangentArrow A.hom (secPt σ))).mapCoeffs (resEquiv σ) (by
      intro c v
      change (resEquiv σ).symm (resEquiv σ c) • v = c • v
      rw [RingEquiv.symm_apply_apply])

instance finiteDimensional_tangentAt [LocallyOfFiniteType A.hom]
    (σ : ArithmeticOfJacobiPolynomials.ComplexRealization.Points A) : FiniteDimensional ℂ
      (TangentAt A σ) :=
  Module.Finite.of_basis (tangentBasis A σ)

/-- Changing from the residue field to `ℂ` preserves the tangent dimension. -/
theorem finrank_tangentAt [LocallyOfFiniteType A.hom]
    (σ : ArithmeticOfJacobiPolynomials.ComplexRealization.Points A) :
    Module.finrank ℂ (TangentAt A σ) =
      Module.finrank (A.left.residueField (secPt σ))
        (DottedTangentArrow A.hom (secPt σ)) := by
  rw [Module.finrank_eq_card_basis (tangentBasis A σ), Fintype.card_fin]

variable [GrpObj A]

/-- The rational first singular homology is finite-dimensional. Finiteness
descends from the real period space by Mathlib's scalar-extension rank formula. -/
theorem UniformizationData.finiteDimensional_bettiOne [LocallyOfFiniteType A.hom]
    (D : UniformizationData A) :
    FiniteDimensional ℚ (ArithmeticOfJacobiPolynomials.ComplexRealization.bettiOne A) := by
  have : FiniteDimensional ℝ (Lie A) := Module.Finite.trans ℂ (Lie A)
  have : FiniteDimensional ℝ (ℝ ⊗[ℚ] ArithmeticOfJacobiPolynomials.ComplexRealization.bettiOne A) :=
    Module.Finite.equiv D.period.symm
  apply Module.rank_lt_aleph0_iff.mp
  have h := Module.rank_lt_aleph0 ℝ (ℝ ⊗[ℚ]
    ArithmeticOfJacobiPolynomials.ComplexRealization.bettiOne A)
  simpa only [Module.rank_baseChange, Cardinal.lift_lt_aleph0] using h

/-- The period isomorphism doubles the complex tangent dimension. -/
theorem UniformizationData.finrank_bettiOne [LocallyOfFiniteType A.hom]
    (D : UniformizationData A) :
    Module.finrank ℚ (ArithmeticOfJacobiPolynomials.ComplexRealization.bettiOne A) =
      2 * Module.finrank ℂ (Lie A) := by
  rw [← Module.finrank_baseChange (R := ℝ), D.period.finrank_eq,
    ← Module.finrank_mul_finrank ℝ ℂ (Lie A), Complex.finrank_real_complex]

/-- For a smooth variety of relative dimension `d`, `H₁(A(ℂ), ℚ)`
has dimension `2d`. -/
theorem UniformizationData.finrank_bettiOne_of_smoothOfRelativeDimension (d : ℕ)
    [SmoothOfRelativeDimension d A.hom] (D : UniformizationData A) :
    Module.finrank ℚ (ArithmeticOfJacobiPolynomials.ComplexRealization.bettiOne A) = 2 * d := by
  have := SmoothOfRelativeDimension.smooth d A.hom
  rw [D.finrank_bettiOne, finrank_tangentAt A (1 :
    ArithmeticOfJacobiPolynomials.ComplexRealization.Points A),
    Scheme.Hom.finrank_dottedTangentArrow_of_smoothOfRelativeDimension A.hom d]

/-- An abelian variety has one geometric dimension `d`, and its rational
first singular homology has dimension `2d`. Smoothness and constant relative
dimension come from Stacks. -/
theorem UniformizationData.exists_dimension_bettiOne [IsAbelianVariety ℂ A]
    (D : UniformizationData A) :
    ∃ d : ℕ, topologicalKrullDim A.left = (d : WithBot ℕ∞) ∧
      Module.finrank ℚ (ArithmeticOfJacobiPolynomials.ComplexRealization.bettiOne A) = 2 * d := by
  have := smooth_of_isAbelianVariety ℂ A
  have : ConnectedSpace A.left :=
    ((isAbelianVariety_iff_isProper_of_connectedSpace_of_geometricallyReduced ℂ A).mp
      inferInstance).2.1
  obtain ⟨d, hd⟩ := exists_smoothOfRelativeDimension_of_connectedSpace A.hom
  have := hd
  exact ⟨d, topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field d A.hom,
    UniformizationData.finrank_bettiOne_of_smoothOfRelativeDimension A d D⟩

/-- The numerical dimension uses the same library dimension as the Jacobian
dimension theorems. -/
theorem UniformizationData.finrank_bettiOne_eq_twice_dimension [IsAbelianVariety ℂ A]
    (D : UniformizationData A) :
    Module.finrank ℚ (ArithmeticOfJacobiPolynomials.ComplexRealization.bettiOne A) =
      2 * Stacks.Groupoids.abelianVarietyDimension A := by
  obtain ⟨d, hd, h⟩ := D.exists_dimension_bettiOne A
  simpa [Stacks.Groupoids.abelianVarietyDimension, hd] using h

/-- Finiteness on every positive power follows from the projection
comparison and finiteness on the original Betti space. -/
theorem UniformizationData.finiteDimensional_bettiPow [LocallyOfFiniteType A.hom]
    (DA : UniformizationData A)
    (D : ∀ h, UniformizationData (ArithmeticOfJacobiPolynomials.GroupScheme.powObj ℂ A (h + 1))) (h
      : ℕ) :
    FiniteDimensional ℚ
      (ArithmeticOfJacobiPolynomials.ComplexRealization.bettiOne
        (ArithmeticOfJacobiPolynomials.GroupScheme.powObj ℂ A (h + 1))) := by
  have := DA.finiteDimensional_bettiOne A
  exact Module.Finite.equiv (bettiPowEquiv A DA D h).symm

/-- The Betti dimension of `A^(h+1)` is `(h+1) dim H₁(A)`. -/
theorem UniformizationData.finrank_bettiPow (DA : UniformizationData A)
    (D : ∀ h, UniformizationData (ArithmeticOfJacobiPolynomials.GroupScheme.powObj ℂ A (h + 1))) (h
      : ℕ) :
    Module.finrank ℚ
      (ArithmeticOfJacobiPolynomials.ComplexRealization.bettiOne
        (ArithmeticOfJacobiPolynomials.GroupScheme.powObj ℂ A (h + 1))) =
      (h + 1) * Module.finrank ℚ (ArithmeticOfJacobiPolynomials.ComplexRealization.bettiOne A) := by
  rw [(bettiPowEquiv A DA D h).finrank_eq]
  simp [Module.finrank]

end ArithmeticOfJacobiPolynomials.AbelianBettiHodge
