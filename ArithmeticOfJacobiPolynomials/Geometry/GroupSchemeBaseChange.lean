/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.AbelianVariety
public import StacksFrontier.AlgebraicGeometry.GroupScheme.BaseChange
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.RepresentingGroup
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Base change of a commutative group scheme along a field extension

Let `K/k` be a field extension and `A : Over (Spec k)` a group object (a group scheme over `k`).

* `ArithmeticOfJacobiPolynomials.GroupScheme.baseChange K A : Over (Spec K)` is `A_K = A ×_{Spec k}
Spec K`, the
  image of `A` under the pullback functor `Over.pullback (Spec K ⟶ Spec k)`. This functor is a
  braided monoidal functor between cartesian monoidal categories (Mathlib's
  `Over.instBraidedPullback`), so `A_K` inherits a group object structure
  (Stacks' `AlgebraicGeometry.GroupScheme.grpObjPullbackObj`, Tag 022T) and, for `A` commutative,
  is commutative (`Functor.isCommMonObj_obj`).
* **Points.** For a further extension `L/K` (with `IsScalarTower k K L`),
  `baseChangePointsEquiv K L A : GeomPoints K L (baseChange K A) ≃+ GeomPoints k L A` is the
  additive bijection `A_K(L) ≅ A(L)` given by the universal property of the pullback
  (the adjunction `Over.map ⊣ Over.pullback`), a group isomorphism by Stacks'
  `AlgebraicGeometry.GroupScheme.pointsMulEquiv` (`toBaseChangeHomMulEquiv`). It is equivariant
  for `σ : L ≃ₐ[K] L` acting on the left and `σ.restrictScalars k : L ≃ₐ[k] L` acting on the right
  (`baseChangePointsEquiv_smul`).
* **Endomorphisms.** `baseChangeEnd K A : GrpObjEnd A →+* GrpObjEnd (baseChange K A)` is
  functoriality of the pullback; it is compatible with the actions on points
  (`baseChangePointsEquiv_geomPointsAction`).
* **Abelian varieties.** `IsAbelianVariety.baseChange`: an abelian variety over `k` stays an
  abelian variety over `K`; this is Stacks' `AlgebraicGeometry.isAbelianVariety_pullbackObj`
  (Tag 0BFB) read for this file's group structure on `A_K`.

This is generic: nothing here is specific to Jacobians.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj

universe u

namespace ArithmeticOfJacobiPolynomials

namespace GroupScheme

open GroupObject

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]

/-- The morphism `Spec K ⟶ Spec k` induced by the field extension `K/k`. -/
noncomputable abbrev specMapAlgebra : Spec (.of K) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

/-- The base change functor `Over (Spec k) ⥤ Over (Spec K)`, `X ↦ X ×_{Spec k} Spec K`. -/
noncomputable abbrev baseChangeFunctor : Over (Spec (.of k)) ⥤ Over (Spec (.of K)) :=
  Over.pullback (specMapAlgebra K)

/-- The base change `A_K = A ×_{Spec k} Spec K` of a scheme `A` over `k` to `K`. -/
noncomputable abbrev baseChange (A : Over (Spec (.of k))) : Over (Spec (.of K)) :=
  (baseChangeFunctor (k := k) K).obj A

variable (A : Over (Spec (.of k)))

section Group

variable [GrpObj A]

-- The group structure on `baseChange K A` is Stacks'
-- `AlgebraicGeometry.GroupScheme.grpObjPullbackObj` (`baseChange K A` is by definition the
-- pullback `(Over.pullback (Spec K ⟶ Spec k)).obj A`).

/-- The base change of a commutative group object is commutative (`Functor.isCommMonObj_obj`
for the braided functor `Over.pullback`). -/
instance baseChange.instIsCommMonObj [IsCommMonObj A] : IsCommMonObj (baseChange K A) :=
  Functor.isCommMonObj_obj (F := baseChangeFunctor (k := k) K)

/-- The concrete field-base-change adapter explicitly uses Mathlib's mapped
monoid-homomorphism instance, since inference does not unfold this abbreviation. -/
instance baseChange.instIsMonHomMap {B : Over (Spec (.of k))} [GrpObj B] (h : B ⟶ B)
    [IsMonHom h] : IsMonHom ((baseChangeFunctor (k := k) K).map h) :=
  CategoryTheory.Functor.map.instIsMonHom (F := baseChangeFunctor (k := k) K)
    (X := B) (Y := B) h

end Group

section Points

variable (L : Type u) [Field L] [Algebra K L] [Algebra k L] [IsScalarTower k K L]

variable (k) in
/-- `Spec L ⟶ Spec K ⟶ Spec k` is `Spec L ⟶ Spec k`. -/
theorem specOver_hom_comp :
    (specOver K L).hom ≫ specMapAlgebra (k := k) K = (specOver k L).hom := by
  change Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k K)) =
    Spec.map (CommRingCat.ofHom (algebraMap k L))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

variable (k) in
/-- `Spec L`, viewed over `Spec k` through `Spec K`, is `specOver k L`. -/
@[expose]
noncomputable def mapSpecOverIso :
    (Over.map (specMapAlgebra (k := k) K)).obj (specOver K L) ≅ specOver k L :=
  Over.isoMk (Iso.refl _) (by
    rw [Iso.refl_hom, Category.id_comp]
    exact (specOver_hom_comp k K L).symm)

variable (k) in
@[simp]
theorem mapSpecOverIso_hom_left : (mapSpecOverIso k K L).hom.left = 𝟙 _ :=
  rfl

/-- The map `A(L) → A_K(L)`, `Q ↦ (Q, Spec L ⟶ Spec K)`, via the universal property of the
pullback (the adjunction `Over.map ⊣ Over.pullback`). -/
@[expose]
noncomputable def toBaseChangeHom (Q : specOver k L ⟶ A) : specOver K L ⟶ baseChange K A :=
  (Over.mapPullbackAdj (specMapAlgebra (k := k) K)).homEquiv _ _
    ((mapSpecOverIso k K L).hom ≫ Q)

theorem toBaseChangeHom_eq (Q : specOver k L ⟶ A) :
    toBaseChangeHom K A L Q =
      (Over.mapPullbackAdj (specMapAlgebra (k := k) K)).unit.app (specOver K L) ≫
        (baseChangeFunctor (k := k) K).map ((mapSpecOverIso k K L).hom ≫ Q) :=
  Adjunction.homEquiv_unit _ _ _ _

/-- `toBaseChangeHom` is natural in `A`. -/
theorem toBaseChangeHom_comp {B : Over (Spec (.of k))} (Q : specOver k L ⟶ A) (g : A ⟶ B) :
    toBaseChangeHom K B L (Q ≫ g) =
      toBaseChangeHom K A L Q ≫ (baseChangeFunctor (k := k) K).map g := by
  rw [toBaseChangeHom, toBaseChangeHom, ← Category.assoc, Adjunction.homEquiv_naturality_right]

variable [GrpObj A] [IsCommMonObj A]

attribute [local instance] Hom.commGroup

omit [IsCommMonObj A] in
/-- **The group isomorphism `A(L) ≃* A_K(L)`** on morphisms: Stacks'
`AlgebraicGeometry.GroupScheme.pointsMulEquiv` (Tag 022T) for `f = Spec K ⟶ Spec k` and
`T = Spec L`, precomposed with the identification `mapSpecOverIso` of `Spec L` over `Spec k`. -/
@[expose]
noncomputable def toBaseChangeHomMulEquiv :
    (specOver k L ⟶ A) ≃* (specOver K L ⟶ baseChange K A) :=
  (Stacks.PicardFunctor.homMulEquivOfIso (mapSpecOverIso k K L)).trans
    (AlgebraicGeometry.GroupScheme.pointsMulEquiv (specMapAlgebra (k := k) K) A
      (specOver K L)).symm

omit [IsCommMonObj A] in
theorem toBaseChangeHomMulEquiv_apply (Q : specOver k L ⟶ A) :
    toBaseChangeHomMulEquiv K A L Q = toBaseChangeHom K A L Q :=
  rfl

omit [IsCommMonObj A] in
/-- `toBaseChangeHom` is multiplicative for the hom-groups (derived from
`toBaseChangeHomMulEquiv`). -/
theorem toBaseChangeHom_mul (P Q : specOver k L ⟶ A) :
    toBaseChangeHom K A L (P * Q) = toBaseChangeHom K A L P * toBaseChangeHom K A L Q :=
  map_mul (toBaseChangeHomMulEquiv K A L) P Q

/-- The map `A(L) → A_K(L)` on points (the inverse of `baseChangePointsEquiv`). -/
@[expose]
noncomputable def toBaseChangePoints (Q : GeomPoints k L A) : GeomPoints K L (baseChange K A) :=
  (GeomPoints.toHom K L (baseChange K A)).symm (toBaseChangeHom K A L (GeomPoints.toHom k L A Q))

omit [GrpObj A] [IsCommMonObj A] in
theorem toHom_toBaseChangePoints (Q : GeomPoints k L A) :
    GeomPoints.toHom K L (baseChange K A) (toBaseChangePoints K A L Q) =
      toBaseChangeHom K A L (GeomPoints.toHom k L A Q) :=
  Equiv.apply_symm_apply _ _

/-- **Points of the base change.** For `L/K/k`, the additive bijection
`A_K(L) ≃ A(L)` (universal property of the fibre product `A_K = A ×_{Spec k} Spec K`). -/
@[expose]
noncomputable def baseChangePointsEquiv : GeomPoints K L (baseChange K A) ≃+ GeomPoints k L A :=
  AddEquiv.symm
    { toFun := toBaseChangePoints K A L
      invFun := fun P => (GeomPoints.toHom k L A).symm
        ((toBaseChangeHomMulEquiv K A L).symm (GeomPoints.toHom K L (baseChange K A) P))
      left_inv := fun Q => by
        dsimp only
        rw [toHom_toBaseChangePoints, ← toBaseChangeHomMulEquiv_apply,
          MulEquiv.symm_apply_apply, Equiv.symm_apply_apply]
      right_inv := fun P => by
        apply (GeomPoints.toHom K L (baseChange K A)).injective
        dsimp only
        rw [toHom_toBaseChangePoints, Equiv.apply_symm_apply, ← toBaseChangeHomMulEquiv_apply,
          MulEquiv.apply_symm_apply]
      map_add' := fun P Q => by
        apply (GeomPoints.toHom K L (baseChange K A)).injective
        rw [toHom_toBaseChangePoints, GeomPoints.toHom_add, GeomPoints.toHom_add,
          toHom_toBaseChangePoints, toHom_toBaseChangePoints]
        exact toBaseChangeHom_mul K A L _ _ }

variable {K A L}

/-- The inverse of `baseChangePointsEquiv` is `toBaseChangePoints`. -/
theorem baseChangePointsEquiv_symm_apply (Q : GeomPoints k L A) :
    (baseChangePointsEquiv K A L).symm Q = toBaseChangePoints K A L Q :=
  rfl

/-- On underlying morphisms, the inverse of `baseChangePointsEquiv` is `toBaseChangeHom`. -/
theorem toHom_baseChangePointsEquiv_symm (Q : GeomPoints k L A) :
    GeomPoints.toHom K L (baseChange K A) ((baseChangePointsEquiv K A L).symm Q) =
      toBaseChangeHom K A L (GeomPoints.toHom k L A Q) :=
  toHom_toBaseChangePoints K A L Q

/-- `Spec σ` over `Spec k` corresponds to `Spec σ` over `Spec K`. -/
theorem mapSpecOverIso_hom_specAut (σ : L ≃ₐ[K] L) :
    (mapSpecOverIso k K L).hom ≫ specAut k L (σ.restrictScalars k) =
      (Over.map (specMapAlgebra (k := k) K)).map (specAut K L σ) ≫ (mapSpecOverIso k K L).hom := by
  have hσ : ((σ.restrictScalars k : L ≃ₐ[k] L) : L →+* L) = (σ : L →+* L) := rfl
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, mapSpecOverIso_hom_left, Over.map_map_left,
    specAut_left, specAut_left, Category.id_comp, Category.comp_id, hσ]

omit [GrpObj A] [IsCommMonObj A] in
/-- `toBaseChangeHom` intertwines the Galois actions. -/
theorem toBaseChangeHom_specAut (σ : L ≃ₐ[K] L) (Q : specOver k L ⟶ A) :
    toBaseChangeHom K A L (specAut k L (σ.restrictScalars k) ≫ Q) =
      specAut K L σ ≫ toBaseChangeHom K A L Q := by
  rw [toBaseChangeHom, toBaseChangeHom, ← Category.assoc, mapSpecOverIso_hom_specAut,
    Category.assoc, Adjunction.homEquiv_naturality_left]

/-- **Galois equivariance.** `baseChangePointsEquiv (σ • P) = σ|_k • baseChangePointsEquiv P`
for `σ : L ≃ₐ[K] L`. -/
theorem baseChangePointsEquiv_smul (σ : L ≃ₐ[K] L) (P : GeomPoints K L (baseChange K A)) :
    baseChangePointsEquiv K A L (σ • P) =
      (σ.restrictScalars k : L ≃ₐ[k] L) • baseChangePointsEquiv K A L P := by
  apply (baseChangePointsEquiv K A L).symm.injective
  apply (GeomPoints.toHom K L (baseChange K A)).injective
  rw [AddEquiv.symm_apply_apply, toHom_baseChangePointsEquiv_symm, GeomPoints.toHom_smul,
    GeomPoints.toHom_smul, toBaseChangeHom_specAut, ← toHom_baseChangePointsEquiv_symm,
    AddEquiv.symm_apply_apply]

end Points

section End

variable [GrpObj A] [IsCommMonObj A]

attribute [local instance] Hom.commGroup

/-- **Base change of endomorphisms.** Functoriality of the pullback gives a ring homomorphism
`End(A) →+* End(A_K)`, `f ↦ f_K`. -/
@[expose]
noncomputable def baseChangeEnd : GrpObjEnd A →+* GrpObjEnd (baseChange K A) where
  toFun f := GrpObjEnd.mk (A := baseChange K A) ((baseChangeFunctor (k := k) K).map f.hom)
  map_one' := GrpObjEnd.ext (by
    rw [GrpObjEnd.hom_mk, GrpObjEnd.hom_one, GrpObjEnd.hom_one,
      CategoryTheory.Functor.map_id])
  map_mul' f g := GrpObjEnd.ext (by
    rw [GrpObjEnd.hom_mk, GrpObjEnd.hom_mul, GrpObjEnd.hom_mul, GrpObjEnd.hom_mk,
      GrpObjEnd.hom_mk, CategoryTheory.Functor.map_comp])
  map_zero' := GrpObjEnd.ext (by
    rw [GrpObjEnd.hom_mk, GrpObjEnd.hom_zero, GrpObjEnd.hom_zero,
      CategoryTheory.Functor.map_one]
    rfl)
  map_add' f g := GrpObjEnd.ext (by
    rw [GrpObjEnd.hom_mk, GrpObjEnd.hom_add, GrpObjEnd.hom_add, GrpObjEnd.hom_mk,
      GrpObjEnd.hom_mk, CategoryTheory.Functor.map_mul]
    rfl)

variable {K A}

/-- The underlying morphism of `f_K` is the pullback of `f`. -/
theorem baseChangeEnd_hom (f : GrpObjEnd A) :
    (baseChangeEnd K A f).hom = (baseChangeFunctor (k := k) K).map f.hom :=
  rfl

variable (L : Type u) [Field L] [Algebra K L] [Algebra k L] [IsScalarTower k K L]

/-- **Compatibility with the actions on points.** Under `A_K(L) ≃ A(L)`, the action of `f_K`
on `A_K(L)` corresponds to the action of `f` on `A(L)`. -/
theorem baseChangePointsEquiv_geomPointsAction (f : GrpObjEnd A)
    (P : GeomPoints K L (baseChange K A)) :
    baseChangePointsEquiv K A L (geomPointsAction K L (baseChange K A) (baseChangeEnd K A f) P) =
      geomPointsAction k L A f (baseChangePointsEquiv K A L P) := by
  apply (baseChangePointsEquiv K A L).symm.injective
  apply (GeomPoints.toHom K L (baseChange K A)).injective
  rw [AddEquiv.symm_apply_apply, toHom_baseChangePointsEquiv_symm, toHom_geomPointsAction,
    toHom_geomPointsAction, toBaseChangeHom_comp, ← toHom_baseChangePointsEquiv_symm,
    AddEquiv.symm_apply_apply, baseChangeEnd_hom]

end End

end GroupScheme

open GroupScheme in
/-- **Abelian varieties are stable under field base change** ([Stacks, Tag 0BFB],
`AlgebraicGeometry.isAbelianVariety_pullbackObj`), for the group structure `grpObjPullbackObj`
on `A_K`. -/
instance IsAbelianVariety.baseChange {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsAbelianVariety k A] :
    IsAbelianVariety K (GroupScheme.baseChange K A) :=
  isAbelianVariety_pullbackObj A

end ArithmeticOfJacobiPolynomials
