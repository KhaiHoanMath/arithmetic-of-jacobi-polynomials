/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.AbelianDuality
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic

/-!
# Polarizations characterized by ample line bundles

Milne, *Abelian Varieties*, §13 and Remark 13.2 define a polarization over `k` by its
geometric realization `a ↦ t_a^* L ⊗ L⁻¹` for an ample line bundle. The homomorphism is
defined over `k`; the ample line bundle need only exist geometrically. The definition
below uses the Poincaré class on the product and Stacks' ampleness predicate
(Tag 01PS).
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace ArithmeticOfJacobiPolynomials.AbelianDuality

variable {k : Type u} [Field k]

/-- A Picard class represented by an ample invertible sheaf, with Stacks Tag 01PS ampleness. -/
def IsAmpleClass (X : Scheme.{u}) (M : Stacks.Picard.ofScheme X) : Prop :=
  ∃ (L : X.Modules) (hL : Stacks.Ample.IsInvertibleModule X L),
    @Stacks.Ample.IsAmple X L hL ∧
      Stacks.SheafOfModules.picardClass X.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) L hL = M

variable (A : Over (Spec (.of k))) [GrpObj A]

/-- The class `t_a^* L ⊗ L⁻¹` induced by a line bundle. -/
def inducedClass (L : Stacks.Picard.ofScheme A.left)
    (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) : Stacks.Picard.ofScheme A.left :=
  Stacks.Picard.schemePullbackClass (translate A a).left L - L

/-- Algebraically trivial twists do not change the induced morphism on points. -/
theorem inducedClass_add_translationInvariant (L N : Stacks.Picard.ofScheme A.left)
    (hN : IsTranslationInvariant A N) (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    inducedClass A (L + N) a = inducedClass A L a := by
  simp only [inducedClass, Stacks.Picard.schemePullbackClass_add, hN a]
  abel

variable (D : Over (Spec (.of k))) [GrpObj D]

/-- A geometric point of `A_Ω` regarded as a geometric point of `A` over `k`. -/
def geometricPoint (Ω : Type u) [Field Ω] [Algebra k Ω]
    (a : 𝟙_ (Over (Spec (.of Ω))) ⟶ GroupScheme.baseChange Ω A) :
    GroupScheme.specOver k Ω ⟶ A :=
  (Over.map (GroupScheme.specMapAlgebra Ω)).map a ≫
    (Over.mapPullbackAdj (GroupScheme.specMapAlgebra Ω)).counit.app A

/-- A homomorphism to the dual is a polarization if, on every algebraically closed
geometric extension, its Poincaré classes are induced by an ample line bundle.
The geometric line bundle is allowed to vary with the extension field. -/
def IsPolarization (P : Stacks.Picard.ofScheme (A ⊗ D).left) (φ : A ⟶ D)
    [IsMonHom φ] : Prop :=
  ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω],
    ∃ L : Stacks.Picard.ofScheme (GroupScheme.baseChange Ω A).left,
      IsAmpleClass (GroupScheme.baseChange Ω A).left L ∧
        ∀ a : 𝟙_ (Over (Spec (.of Ω))) ⟶ GroupScheme.baseChange Ω A,
          Stacks.Picard.schemePullbackClass
              (familyFibreMap A D Ω (geometricPoint A Ω a ≫ φ)) P =
            inducedClass (GroupScheme.baseChange Ω A) L a

/-- A principal polarization is a polarization that is an isomorphism of group schemes. -/
structure IsPrincipalPolarization (P : Stacks.Picard.ofScheme (A ⊗ D).left)
    (φ : A ⟶ D) [IsMonHom φ] : Prop where
  isPolarization : IsPolarization A D P φ
  isIso : IsIso φ

end ArithmeticOfJacobiPolynomials.AbelianDuality
