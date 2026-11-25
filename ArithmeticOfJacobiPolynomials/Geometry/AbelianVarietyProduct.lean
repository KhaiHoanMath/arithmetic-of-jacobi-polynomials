/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.AbelianVariety
public import ArithmeticOfJacobiPolynomials.Geometry.GroupSchemeProduct
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVarietyZero
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Products and powers of abelian varieties

Let `K` be a field.

* `geometricallyReduced_comp_of_flat`: if `f : X ⟶ Y` is geometrically reduced and flat and
  `g : Y ⟶ Z` is geometrically reduced and locally of finite type, then `f ≫ g` is geometrically
  reduced (Stacks 035Z in the locally noetherian case: over a field, `X_L → Y_L` is flat with
  reduced fibres over the reduced locally noetherian scheme `Y_L`, so `X_L` is reduced; this is
  Mathlib's `GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian`).
* `geometricallyIntegral_comp`: the same for geometric integrality, adding universal openness of
  both maps (Mathlib's `GeometricallyIrreducible.comp`, Stacks 038F).
* `flat_of_field`: every morphism of schemes to `Spec K` is flat.
* `geometricallyIntegral_tensorObj_hom`: if `A`, `B` are geometrically integral and locally of
  finite type over `K`, so is `A ⊗ B = A ×_K B` (the structure map `A ×_K B → A → Spec K` is a
  composite of the base change of `B → Spec K` and of `A → Spec K`; both are flat and locally of
  finite presentation over the field `K`, hence universally open).
* `geometricallyIntegral_id`: identities are geometrically integral.
* `IsAbelianVariety.tensorObj`, `IsAbelianVariety.powObj`: products of abelian varieties and the
  powers `A^h` (`GroupScheme.powObj`) of an abelian variety are abelian varieties (the point
  `Spec K` is Stacks' `AlgebraicGeometry.isAbelianVariety_tensorUnit`); the predicate is Stacks'
  `AlgebraicGeometry.IsAbelianVariety`.

No statement about the dimension of a product is made here.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry

universe u

namespace ArithmeticOfJacobiPolynomials

section Composition

variable {X Y Z : Scheme.{u}}

/-- **Geometric reducedness is stable under composition** with a flat first map and a locally
of finite type second map: for a field `L` and `Spec L ⟶ Z`, the base change
`X_L = X ×_Y Y_L → Y_L` is flat and geometrically reduced over the reduced locally noetherian
scheme `Y_L`, hence `X_L` is reduced. -/
theorem geometricallyReduced_comp_of_flat (f : X ⟶ Y) (g : Y ⟶ Z) [GeometricallyReduced f]
    [GeometricallyReduced g] [Flat f] [LocallyOfFiniteType g] :
    GeometricallyReduced (f ≫ g) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun L _ x ↦ ?_⟩
  have : IsReduced (pullback g x) :=
    pullback_of_geometrically (GeometricallyReduced.geometrically_isReduced (f := g)) L x
  have : IsLocallyNoetherian (pullback g x) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd g x)
  have : IsReduced (pullback f (pullback.fst g x)) :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
      (pullback.snd f (pullback.fst g x))
  exact isReduced_of_isOpenImmersion (pullbackRightPullbackFstIso g x f).inv

/-- **Geometric integrality is stable under composition** when the first map is flat, both maps
are universally open and the second map is locally of finite type. -/
theorem geometricallyIntegral_comp (f : X ⟶ Y) (g : Y ⟶ Z) [GeometricallyIntegral f]
    [GeometricallyIntegral g] [Flat f] [UniversallyOpen f] [UniversallyOpen g]
    [LocallyOfFiniteType g] : GeometricallyIntegral (f ≫ g) := by
  have := geometricallyReduced_comp_of_flat f g
  have := GeometricallyIrreducible.comp f g
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible (f := f ≫ g)

/-- Identities are geometrically integral. -/
theorem geometricallyIntegral_id (X : Scheme.{u}) : GeometricallyIntegral (𝟙 X) := by
  have key : ∀ (L : Type u) [Field L] (y : Spec (.of L) ⟶ X),
      IsIntegral (pullback (𝟙 X) y) := by
    intro L _ y
    have := (IsPullback.of_hasPullback (𝟙 X) y).isIso_snd_of_isIso
    exact IsIntegral.of_isIso (inv (pullback.snd (𝟙 X) y))
  have : GeometricallyReduced (𝟙 X) :=
    ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun L _ y ↦ by
      have := key L y
      exact inferInstanceAs (IsReduced (pullback (𝟙 X) y))⟩
  have : GeometricallyIrreducible (𝟙 X) :=
    ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun L _ y ↦ by
      have := key L y
      exact inferInstanceAs (IrreducibleSpace (pullback (𝟙 X) y : Scheme.{u}))⟩
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible (f := 𝟙 X)

end Composition

section Product

variable {K : Type u} [Field K]

/-- Every morphism of schemes to the spectrum of a field is flat. -/
theorem flat_of_field {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) : Flat f := by
  have hK : IsField Γ(Spec (CommRingCat.of K), ⊤) := MulEquiv.isField (Field.toIsField K)
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv
  exact (HasRingHomProperty.iff_of_source_openCover (P := @Flat) X.affineCover).mpr
    fun _ ↦ RingHom.Flat.of_isField hK _

/-- **The product of two geometrically integral `K`-schemes locally of finite type is
geometrically integral.** The structure map of `A ⊗ B = A ×_K B` is
`pullback.fst A.hom B.hom ≫ A.hom`, where `pullback.fst A.hom B.hom` is a base change of
`B.hom`; both maps are flat and locally of finite presentation (over a field), hence universally
open. -/
theorem geometricallyIntegral_tensorObj_hom (A B : Over (Spec (.of K)))
    [GeometricallyIntegral A.hom] [GeometricallyIntegral B.hom]
    [LocallyOfFiniteType A.hom] [LocallyOfFiniteType B.hom] :
    GeometricallyIntegral (A ⊗ B).hom := by
  have := flat_of_field A.hom
  have := flat_of_field B.hom
  have : LocallyOfFinitePresentation A.hom := inferInstance
  have : LocallyOfFinitePresentation B.hom := inferInstance
  rw [Over.tensorObj_hom]
  exact geometricallyIntegral_comp _ _

/-- A group scheme over a field whose structure map is proper and geometrically integral is an
abelian variety (the variety structure comes from geometric integrality: a geometrically
integral scheme over a field is integral). -/
theorem isAbelianVariety_of_isProper_of_geometricallyIntegral {A : Over (Spec (.of K))} [GrpObj A]
    [IsProper A.hom] [GeometricallyIntegral A.hom] : IsAbelianVariety K A :=
  haveI : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton (f := A.hom)
  { toIsProperVariety :=
      (isProperVariety_iff K A.hom).2 ⟨{ toIsIntegral := this }, inferInstance⟩
    toGeometricallyIntegral := inferInstance }

/-- **The product of two abelian varieties is an abelian variety.** -/
instance IsAbelianVariety.tensorObj {A B : Over (Spec (CommRingCat.of K))} [GrpObj A] [GrpObj B]
    [IsAbelianVariety K A] [IsAbelianVariety K B] : IsAbelianVariety K (A ⊗ B) :=
  haveI : IsProper (A ⊗ B).hom := GroupScheme.isProper_tensorObj_hom A B
  haveI : GeometricallyIntegral (A ⊗ B).hom := geometricallyIntegral_tensorObj_hom A B
  isAbelianVariety_of_isProper_of_geometricallyIntegral

/-- **Powers of an abelian variety are abelian varieties:** `A^h = A ⊗ (A ⊗ (⋯ ⊗ 𝟙_))`
(`GroupScheme.powObj K A h`); for `h = 0` this is `Spec K` (Stacks'
`AlgebraicGeometry.isAbelianVariety_tensorUnit`). -/
instance IsAbelianVariety.powObj {A : Over (Spec (CommRingCat.of K))} [GrpObj A]
    [IsAbelianVariety K A] (h : ℕ) : IsAbelianVariety K (GroupScheme.powObj K A h) := by
  induction h with
  | zero => exact inferInstanceAs (IsAbelianVariety K (𝟙_ (Over (Spec (CommRingCat.of K)))))
  | succ h ih => exact IsAbelianVariety.tensorObj (B := GroupScheme.powObj K A h)

end Product

end ArithmeticOfJacobiPolynomials
