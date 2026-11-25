/- Assembled by AxiomProver. -/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ArithmeticOfJacobiPolynomials.Geometry.GroupSchemeGeometricPoints
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.IsogenyKernelCount

/-!
# The endomorphism ring of a commutative group object and its action on points

Let `C` be a cartesian monoidal (braided) category and `A` a commutative group object of `C`
(`[GrpObj A] [IsCommMonObj A]`), e.g. a commutative group scheme `A : Over (Spec K)`.

* `ArithmeticOfJacobiPolynomials.GroupObject.GrpObjEnd A` is the type of group-object endomorphisms
of `A`, the
  morphisms `f : A ⟶ A` with `IsMonHom f` (the endomorphisms of `A` in `CommGrp C`). It is a ring
  (`GrpObjEnd.instRing`): the sum `f + g` is the pointwise product `f * g` in the commutative
  hom-group `Hom(A, A)` induced by the group object `A` (`GrpObjEnd.hom_add`), and the product is
  composition, `(f * g).hom = g.hom ≫ f.hom` (`GrpObjEnd.hom_mul`), i.e. `f * g = f ∘ g`.
  Sums of homomorphisms are homomorphisms by `Stacks.Groupoids.isMonHom_mul`; the left
  distributive law uses that `f` is a homomorphism.
* `ArithmeticOfJacobiPolynomials.GroupObject.pointsAction A T`, a ring homomorphism
  `GrpObjEnd A →+* AddMonoid.End (Additive (T ⟶ A))`, is the action on `T`-valued points by
  postcomposition, `P ↦ P ≫ f`.
* `ArithmeticOfJacobiPolynomials.GroupScheme.geomPointsAction K L A`, a ring homomorphism
  `GrpObjEnd A →+* AddMonoid.End (GeomPoints K L A)`, is the same action on the `L`-points
  `A(L)` of a commutative group scheme over `K`; it commutes with the Galois action
  (`geomPointsAction_smul`).

This is generic: no statement about any specific `A` (no Jacobian, no computation of the
endomorphism ring) is made here.
-/

public section

open CategoryTheory MonoidalCategory SemiCartesianMonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj

universe v u

namespace ArithmeticOfJacobiPolynomials

namespace GroupObject

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

attribute [local instance] Hom.commGroup

section Closure

variable {N M : C} [MonObj N] [GrpObj M]

omit [MonObj N] in
/-- `(h ⊗ h) ≫ μ = (fst ≫ h) * (snd ≫ h)` in the hom-monoid `Hom(N ⊗ N, M)`. -/
theorem tensorHom_comp_mul (h : N ⟶ M) :
    (h ⊗ₘ h) ≫ (MonObj.mul : M ⊗ M ⟶ M) = fst N N ≫ h * snd N N ≫ h := by
  rw [MonObj.mul_eq_mul M, MonObj.comp_mul, tensorHom_fst, tensorHom_snd]

/-- A morphism `h : N ⟶ M` into a group object is a homomorphism iff it preserves
the unit and `μ ≫ h = (fst ≫ h) * (snd ≫ h)`. -/
theorem isMonHom_iff (h : N ⟶ M) :
    IsMonHom h ↔ (MonObj.one : 𝟙_ C ⟶ N) ≫ h = MonObj.one ∧
      (MonObj.mul : N ⊗ N ⟶ N) ≫ h = fst N N ≫ h * snd N N ≫ h := by
  constructor
  · intro hh
    refine ⟨IsMonHom.one_hom h, ?_⟩
    rw [MonObj.mul_eq_mul N, MonObj.mul_comp]
  · rintro ⟨h1, h2⟩
    exact { one_hom := h1, mul_hom := h2.trans (tensorHom_comp_mul h).symm }

/-- The unit `1 : N ⟶ M` of the hom-group is a homomorphism. -/
theorem isMonHom_one : IsMonHom (1 : N ⟶ M) := by
  rw [isMonHom_iff]
  refine ⟨?_, ?_⟩
  · rw [MonObj.comp_one, MonObj.one_eq_one]
  · simp only [MonObj.comp_one, mul_one]

/-- The pointwise inverse of a homomorphism into a commutative group object is a
homomorphism. -/
theorem isMonHom_inv [BraidedCategory C] [IsCommMonObj M] {f : N ⟶ M} (hf : IsMonHom f) :
    IsMonHom f⁻¹ := by
  rw [isMonHom_iff] at hf ⊢
  refine ⟨?_, ?_⟩
  · simp only [GrpObj.comp_inv]
    rw [hf.1, MonObj.one_eq_one, inv_one]
  · simp only [GrpObj.comp_inv]
    rw [hf.2, mul_inv]

end Closure

variable [BraidedCategory C] (A : C) [GrpObj A] [IsCommMonObj A]

/-- The additive subgroup of `Additive (A ⟶ A)` (the hom-group written additively) consisting of
the group-object endomorphisms `f` (`IsMonHom f`). -/
@[expose]
def endAddSubgroup : AddSubgroup (Additive (A ⟶ A)) where
  carrier := {f | IsMonHom (Additive.toMul f)}
  add_mem' {f g} hf hg := by
    have : IsMonHom (Additive.toMul f) := hf
    have : IsMonHom (Additive.toMul g) := hg
    exact Stacks.Groupoids.isMonHom_mul (Additive.toMul f) (Additive.toMul g)
  zero_mem' := isMonHom_one
  neg_mem' hf := isMonHom_inv hf

variable {A} in
/-- Membership in `endAddSubgroup A`. -/
theorem mem_endAddSubgroup {f : Additive (A ⟶ A)} :
    f ∈ endAddSubgroup A ↔ IsMonHom (Additive.toMul f) :=
  Iff.rfl

/-- The endomorphisms of the commutative group object `A`: morphisms `f : A ⟶ A` with
`IsMonHom f`, i.e. the endomorphisms of `A` in `CommGrp C`. It is a ring under the pointwise
group law and composition (`GrpObjEnd.instRing`). -/
@[expose]
def GrpObjEnd : Type v :=
  endAddSubgroup A

namespace GrpObjEnd

variable {A}

/-- The underlying morphism `A ⟶ A` of a group-object endomorphism. -/
@[expose]
def hom (f : GrpObjEnd A) : A ⟶ A :=
  Additive.toMul (Subtype.val f)

/-- The underlying morphism of a group-object endomorphism is a homomorphism. -/
instance isMonHom_hom (f : GrpObjEnd A) : IsMonHom f.hom :=
  mem_endAddSubgroup.1 (Subtype.property f)

/-- The group-object endomorphism attached to a homomorphism `h : A ⟶ A`. -/
@[expose]
def mk (h : A ⟶ A) [IsMonHom h] : GrpObjEnd A :=
  (⟨Additive.ofMul h, mem_endAddSubgroup.2 ‹IsMonHom h›⟩ : endAddSubgroup A)

/-- `(mk h).hom = h`. -/
@[simp]
theorem hom_mk (h : A ⟶ A) [IsMonHom h] : (mk h).hom = h :=
  rfl

/-- Two group-object endomorphisms with the same underlying morphism are equal. -/
@[ext]
theorem ext {f g : GrpObjEnd A} (h : f.hom = g.hom) : f = g :=
  Subtype.ext (Additive.toMul.injective h)

/-- `GrpObjEnd A` is determined by underlying morphisms. -/
theorem hom_injective : Function.Injective (hom : GrpObjEnd A → (A ⟶ A)) :=
  fun _ _ h => ext h

variable (A) in
/-- The additive group structure: pointwise group law of `Hom(A, A)`. -/
noncomputable instance instAddCommGroup : AddCommGroup (GrpObjEnd A) :=
  inferInstanceAs (AddCommGroup (endAddSubgroup A))

variable (A) in
/-- The identity endomorphism. -/
noncomputable instance instOne : One (GrpObjEnd A) :=
  ⟨mk (𝟙 A)⟩

variable (A) in
/-- Multiplication is composition: `f * g = f ∘ g`, i.e. `g ≫ f`. -/
noncomputable instance instMul : Mul (GrpObjEnd A) :=
  ⟨fun f g => mk (g.hom ≫ f.hom)⟩

/-- Addition is the pointwise product in the hom-group `Hom(A, A)`. -/
theorem hom_add (f g : GrpObjEnd A) : (f + g).hom = f.hom * g.hom :=
  rfl

/-- The zero endomorphism is the unit `A ⟶ 𝟙_ ⟶ A` of the hom-group. -/
theorem hom_zero : (0 : GrpObjEnd A).hom = 1 :=
  rfl

/-- Negation is the pointwise inverse in the hom-group `Hom(A, A)`. -/
theorem hom_neg (f : GrpObjEnd A) : (-f).hom = f.hom⁻¹ :=
  rfl

/-- The product `f * g` is the composite `g ≫ f` (that is, `f ∘ g`). -/
theorem hom_mul (f g : GrpObjEnd A) : (f * g).hom = g.hom ≫ f.hom :=
  rfl

/-- The unit is the identity of `A`. -/
theorem hom_one : (1 : GrpObjEnd A).hom = 𝟙 A :=
  rfl

variable (A) in
/-- **The endomorphism ring of a commutative group object.** Addition is the pointwise group law
of `Hom(A, A)`, multiplication is composition (`f * g = g ≫ f`). -/
noncomputable instance instRing : Ring (GrpObjEnd A) where
  __ := instAddCommGroup A
  mul f g := f * g
  one := 1
  mul_assoc f g h := ext (Category.assoc h.hom g.hom f.hom).symm
  one_mul f := ext (Category.comp_id f.hom)
  mul_one f := ext (Category.id_comp f.hom)
  left_distrib f g h := ext (MonObj.mul_comp g.hom h.hom f.hom)
  right_distrib f g h := ext (MonObj.comp_mul h.hom f.hom g.hom)
  zero_mul f := ext (MonObj.comp_one f.hom)
  mul_zero f := ext (MonObj.one_comp f.hom)

end GrpObjEnd

section Points

variable {A}

/-- Postcomposition `P ↦ P ≫ f` with a group-object endomorphism, as an additive endomorphism of
the group `Additive (T ⟶ A)` of `T`-valued points. -/
@[expose]
noncomputable def postcompAddHom (T : C) (f : GrpObjEnd A) :
    Additive (T ⟶ A) →+ Additive (T ⟶ A) where
  toFun P := Additive.ofMul (Additive.toMul P ≫ f.hom)
  map_zero' := MonObj.one_comp f.hom
  map_add' P Q := MonObj.mul_comp (Additive.toMul P) (Additive.toMul Q) f.hom

/-- `postcompAddHom T f P = P ≫ f`. -/
theorem toMul_postcompAddHom (T : C) (f : GrpObjEnd A) (P : Additive (T ⟶ A)) :
    Additive.toMul (postcompAddHom T f P) = Additive.toMul P ≫ f.hom :=
  rfl

variable (A) in
/-- **Action of `End(A)` on `T`-valued points.** Postcomposition `P ↦ P ≫ f` is a ring
homomorphism `End(A) →+* End(A(T))`. -/
@[expose]
noncomputable def pointsAction (T : C) : GrpObjEnd A →+* AddMonoid.End (Additive (T ⟶ A)) where
  toFun f := postcompAddHom T f
  map_one' := AddMonoidHom.ext fun P => Category.comp_id (Additive.toMul P)
  map_mul' f g := AddMonoidHom.ext fun P =>
    (Category.assoc (Additive.toMul P) g.hom f.hom).symm
  map_zero' := AddMonoidHom.ext fun P => MonObj.comp_one (Additive.toMul P)
  map_add' f g := AddMonoidHom.ext fun P => MonObj.comp_mul (Additive.toMul P) f.hom g.hom

/-- `pointsAction A T f P = P ≫ f`. -/
theorem toMul_pointsAction (T : C) (f : GrpObjEnd A) (P : Additive (T ⟶ A)) :
    Additive.toMul (pointsAction A T f P) = Additive.toMul P ≫ f.hom :=
  rfl

/-- The action on points commutes with precomposition by any `u : T' ⟶ T`. -/
theorem pointsAction_precomp {T T' : C} (u : T' ⟶ T) (f : GrpObjEnd A) (P : Additive (T ⟶ A)) :
    pointsAction A T' f (Additive.ofMul (u ≫ Additive.toMul P)) =
      Additive.ofMul (u ≫ Additive.toMul (pointsAction A T f P)) :=
  Category.assoc u (Additive.toMul P) f.hom

end Points

end GroupObject

namespace GroupScheme

open AlgebraicGeometry GroupObject

variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]
  (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]

/-- The image `P ≫ f` of an `L`-point `P` of `A` under a group-object endomorphism `f`. -/
@[expose]
noncomputable def geomPointsMap (f : GrpObjEnd A) (P : GeomPoints K L A) : GeomPoints K L A :=
  (GeomPoints.toHom K L A).symm (GeomPoints.toHom K L A P ≫ f.hom)

variable {K L A} in
/-- On underlying morphisms, `geomPointsMap K L A f P = P ≫ f`. -/
theorem toHom_geomPointsMap (f : GrpObjEnd A) (P : GeomPoints K L A) :
    GeomPoints.toHom K L A (geomPointsMap K L A f P) = GeomPoints.toHom K L A P ≫ f.hom :=
  (GeomPoints.toHom K L A).apply_symm_apply _

/-- A group-object endomorphism `f` of `A` acts additively on `A(L)`, by `P ↦ P ≫ f`. -/
@[expose]
noncomputable def geomPointsAddHom (f : GrpObjEnd A) : GeomPoints K L A →+ GeomPoints K L A where
  toFun := geomPointsMap K L A f
  map_zero' := (GeomPoints.toHom K L A).injective (by
    rw [toHom_geomPointsMap, GeomPoints.toHom_zero, MonObj.one_comp])
  map_add' P Q := (GeomPoints.toHom K L A).injective (by
    rw [toHom_geomPointsMap, GeomPoints.toHom_add, GeomPoints.toHom_add, toHom_geomPointsMap,
      toHom_geomPointsMap, MonObj.mul_comp])

/-- **Action of `End(A)` on the `L`-points `A(L)`.** Postcomposition `P ↦ P ≫ f` gives a ring
homomorphism `End(A) →+* End(A(L))`. -/
@[expose]
noncomputable def geomPointsAction : GrpObjEnd A →+* AddMonoid.End (GeomPoints K L A) where
  toFun f := geomPointsAddHom K L A f
  map_one' := AddMonoidHom.ext fun P => (GeomPoints.toHom K L A).injective (by
    change GeomPoints.toHom K L A (geomPointsMap K L A 1 P) = GeomPoints.toHom K L A P
    rw [toHom_geomPointsMap]
    exact Category.comp_id _)
  map_mul' f g := AddMonoidHom.ext fun P => (GeomPoints.toHom K L A).injective (by
    change GeomPoints.toHom K L A (geomPointsMap K L A (f * g) P) =
      GeomPoints.toHom K L A (geomPointsMap K L A f (geomPointsMap K L A g P))
    rw [toHom_geomPointsMap, toHom_geomPointsMap, toHom_geomPointsMap]
    exact (Category.assoc (GeomPoints.toHom K L A P) g.hom f.hom).symm)
  map_zero' := AddMonoidHom.ext fun P => (GeomPoints.toHom K L A).injective (by
    change GeomPoints.toHom K L A (geomPointsMap K L A 0 P) =
      GeomPoints.toHom K L A (0 : GeomPoints K L A)
    rw [toHom_geomPointsMap, GeomPoints.toHom_zero]
    exact MonObj.comp_one _)
  map_add' f g := AddMonoidHom.ext fun P => (GeomPoints.toHom K L A).injective (by
    change GeomPoints.toHom K L A (geomPointsMap K L A (f + g) P) =
      GeomPoints.toHom K L A (geomPointsMap K L A f P + geomPointsMap K L A g P)
    rw [toHom_geomPointsMap, GeomPoints.toHom_add, toHom_geomPointsMap, toHom_geomPointsMap]
    exact MonObj.comp_mul _ _ _)

variable {K L A}

/-- `geomPointsAction K L A f P = geomPointsMap K L A f P`. -/
theorem geomPointsAction_apply (f : GrpObjEnd A) (P : GeomPoints K L A) :
    geomPointsAction K L A f P = geomPointsMap K L A f P :=
  rfl

/-- On underlying morphisms, `f` acts on `A(L)` by `P ↦ P ≫ f`. -/
theorem toHom_geomPointsAction (f : GrpObjEnd A) (P : GeomPoints K L A) :
    GeomPoints.toHom K L A (geomPointsAction K L A f P) = GeomPoints.toHom K L A P ≫ f.hom :=
  toHom_geomPointsMap f P

/-- **The action of `End(A)` on `A(L)` commutes with the Galois action:**
`f (σ • P) = σ • f P`. -/
theorem geomPointsAction_smul (f : GrpObjEnd A) (σ : L ≃ₐ[K] L) (P : GeomPoints K L A) :
    geomPointsAction K L A f (σ • P) = σ • geomPointsAction K L A f P :=
  (GeomPoints.toHom K L A).injective (by
    rw [toHom_geomPointsAction, GeomPoints.toHom_smul, GeomPoints.toHom_smul,
      toHom_geomPointsAction, Category.assoc])

end GroupScheme

end ArithmeticOfJacobiPolynomials
