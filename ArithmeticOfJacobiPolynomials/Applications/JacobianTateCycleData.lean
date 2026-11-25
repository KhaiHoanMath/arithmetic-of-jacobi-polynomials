/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Applications.JacobianTateCycleWitnesses
public import ArithmeticOfJacobiPolynomials.Geometry.EtaleCycleClassInterface
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence

/-!
# Realized Tate cycle systems on the manuscript Jacobian powers

The general cited cycle-system existence input applies to every
number-field base change of every positive Jacobian power (Corollary 6.6).
Stacks supplies the site and geometric properties; the proved dimension
and primitive-root witnesses verify the remaining hypotheses.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj

namespace ArithmeticOfJacobiPolynomials

open GroupScheme AbelianEtale AbelianCycleClass EtaleCycleClassInterface

namespace JacobianSetting

variable {f : ℚ[X]} (S : JacobianSetting f)

/-- Realized canonical cycle systems for every number field, prime and power. -/
def TateCycleData : Prop :=
  letI := S.isJacobian.isAbelianVariety
  ∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E]
    (ℓ : ℕ) [Fact ℓ.Prime] (h : ℕ),
    let A := ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap ℚ E)))).obj
      (powObj ℚ S.J.X (h + 1)))
    letI := LocallyOfFiniteType.isLocallyNoetherian A.hom
    letI := QuasiCompact.compactSpace_of_compactSpace A.hom
    letI : IsNoetherian A.left := ⟨⟩
    ∃ (B : BigEtaleSite.{0}) (hX : B.Contains A.left),
      have := jacobianEllAdicSite B ℓ
      ∃ ζ : RootSystem ℓ (AlgebraicClosure ℚ),
        Nonempty (CanonicalCycleSystem B ℓ (B.obj A.left hX) A.hom
          (AlgebraicClosure ℚ) ζ ((h + 1) * ((f.natDegree - 1) / 2)))

/-- Canonical cycle systems exist on the number-field base changes of
all positive powers, with the manuscript's genus and codimension convention. -/
theorem exists_tateCycleSystem (hCycle : CanonicalCycleSystemExists)
    (hf : f.Separable) (hd : 0 < f.natDegree)
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E]
    (ℓ : ℕ) [Fact ℓ.Prime] (h : ℕ) :
    letI := S.isJacobian.isAbelianVariety
    let A := ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap ℚ E)))).obj
      (powObj ℚ S.J.X (h + 1)))
    letI := LocallyOfFiniteType.isLocallyNoetherian A.hom
    letI := QuasiCompact.compactSpace_of_compactSpace A.hom
    letI : IsNoetherian A.left := ⟨⟩
    ∃ (B : BigEtaleSite.{0}) (hX : B.Contains A.left),
      have := jacobianEllAdicSite B ℓ
      ∃ ζ : RootSystem ℓ (AlgebraicClosure ℚ),
        Nonempty (CanonicalCycleSystem B ℓ (B.obj A.left hX) A.hom
          (AlgebraicClosure ℚ) ζ ((h + 1) * ((f.natDegree - 1) / 2))) := by
  have := S.isJacobian.isAbelianVariety
  let A := ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap ℚ E)))).obj
    (powObj ℚ S.J.X (h + 1)))
  have : IsAbelianVariety E A := inferInstance
  have : Smooth A.hom := smooth_of_isAbelianVariety E A
  have := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : IsNoetherian A.left := ⟨⟩
  obtain ⟨B, hX⟩ := BigEtaleSite.exists_contains A.left
  have := jacobianEllAdicSite B ℓ
  obtain ⟨ζ⟩ := exists_jacobianRootSystem ℓ
  refine ⟨B, hX, ζ, ?_⟩
  exact hCycle B ℓ (B.obj A.left hX) A.hom (AlgebraicClosure ℚ)
    (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime ℓ).ne_zero) ζ _
    (S.relativeDimension_numberFieldPower hf hd E (h + 1)) inferInstance

/-- The general cited existence theorem applies to all realized Tate targets. -/
theorem tateCycleData (hCycle : CanonicalCycleSystemExists)
    (hf : f.Separable) (hd : 0 < f.natDegree) : S.TateCycleData := by
  intro E _ ℓ _ h
  exact S.exists_tateCycleSystem hCycle hf hd E ℓ h

end JacobianSetting

end ArithmeticOfJacobiPolynomials
