/- Assembled by AxiomProver. -/
module

public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Geometric points of a commutative group scheme, with the Galois action

Let `K` be a field, `L` a field extension of `K` (for instance `AlgebraicClosure K`) and
`A : Over (Spec K)` a commutative group object (a commutative group scheme over `K`; for an
abelian variety the commutativity is
`AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`).

* `ArithmeticOfJacobiPolynomials.GroupScheme.specOver K L` is `Spec L` viewed as a scheme over
`Spec K`.
* `ArithmeticOfJacobiPolynomials.GroupScheme.GeomPoints K L A` is the type of `K`-morphisms `Spec L
⟶ A`, i.e. the
  `L`-points `A(L)`, written additively. Its commutative group law is the one induced on
  `Hom(Spec L, A)` by the group object structure of `A` (`CategoryTheory.Hom.commGroup`; see
  `GeomPoints.toHom_add`, `GeomPoints.toHom_add_eq_lift`).
* `ArithmeticOfJacobiPolynomials.GroupScheme.specAut K L σ` is the automorphism `Spec σ` of `Spec
L` over `Spec K`
  attached to `σ : L ≃ₐ[K] L`. By contravariance of `Spec`,
  `specAut (σ * τ) = specAut σ ≫ specAut τ`, so precomposition `P ↦ Spec σ ≫ P` is a *left*
  action of `L ≃ₐ[K] L` on `A(L)` (on coordinates it applies `σ`). It acts by group
  automorphisms: the instance `DistribMulAction (L ≃ₐ[K] L) (GeomPoints K L A)`.
* The `n`-torsion subgroups `AddSubgroup.torsionBy (GeomPoints K L A) n` are stable
  (`GeomPoints.smul_mem_torsionBy`) and inherit the action, and the multiplication-by-`ℓ` maps
  `A(L)[ℓ^(n+1)] → A(L)[ℓ^n]` (`GeomPoints.torsionMulMap`) are equivariant
  (`GeomPoints.torsionMulMap_smul`).

This is a generic construction: nothing here is specific to Jacobians, and no torsion ranks,
continuity (profinite topology on the Galois group) or Weil pairing are treated.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj

universe u

namespace ArithmeticOfJacobiPolynomials

namespace GroupScheme

variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]

/-- `Spec L` as a scheme over `Spec K`, via `Spec (algebraMap K L)`. -/
noncomputable abbrev specOver : Over (Spec (.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- `Spec` of the identity automorphism of `L` is the identity. -/
theorem specMap_algEquiv_one :
    Spec.map (CommRingCat.ofHom ((1 : L ≃ₐ[K] L) : L →+* L)) = 𝟙 (Spec (.of L)) := by
  have h : CommRingCat.ofHom ((1 : L ≃ₐ[K] L) : L →+* L) = 𝟙 (CommRingCat.of L) := by
    ext x
    rfl
  rw [h, Spec.map_id]

/-- `Spec` reverses composition: `Spec (σ * τ) = Spec σ ≫ Spec τ`. -/
theorem specMap_algEquiv_mul (σ τ : L ≃ₐ[K] L) :
    Spec.map (CommRingCat.ofHom ((σ * τ : L ≃ₐ[K] L) : L →+* L)) =
      Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫
        Spec.map (CommRingCat.ofHom (τ : L →+* L)) := by
  have h : CommRingCat.ofHom ((σ * τ : L ≃ₐ[K] L) : L →+* L) =
      CommRingCat.ofHom (τ : L →+* L) ≫ CommRingCat.ofHom (σ : L →+* L) := by
    ext x
    rfl
  rw [h, Spec.map_comp]

/-- The automorphism `Spec σ` of `Spec L` over `Spec K` attached to `σ : L ≃ₐ[K] L`. -/
@[expose]
noncomputable def specAut (σ : L ≃ₐ[K] L) : specOver K L ⟶ specOver K L :=
  Over.homMk (Spec.map (CommRingCat.ofHom (σ : L →+* L))) (by
    have h : CommRingCat.ofHom (algebraMap K L) ≫ CommRingCat.ofHom (σ : L →+* L) =
        CommRingCat.ofHom (algebraMap K L) := by
      ext x
      exact σ.commutes x
    change Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L)) =
      Spec.map (CommRingCat.ofHom (algebraMap K L))
    rw [← Spec.map_comp, h])

variable {K L} in
/-- The underlying morphism of schemes of `specAut K L σ` is `Spec σ`. -/
@[simp]
theorem specAut_left (σ : L ≃ₐ[K] L) :
    (specAut K L σ).left = Spec.map (CommRingCat.ofHom (σ : L →+* L)) :=
  rfl

/-- `specAut K L 1` is the identity. -/
@[simp]
theorem specAut_one : specAut K L 1 = 𝟙 (specOver K L) := by
  apply Over.OverMorphism.ext
  rw [specAut_left, Over.id_left]
  exact specMap_algEquiv_one K L

/-- `specAut` turns multiplication of automorphisms into composition in the same order. -/
theorem specAut_mul (σ τ : L ≃ₐ[K] L) :
    specAut K L (σ * τ) = specAut K L σ ≫ specAut K L τ := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, specAut_left, specAut_left, specAut_left]
  exact specMap_algEquiv_mul K L σ τ

variable (A : Over (Spec (.of K)))

/-- The `L`-valued points `A(L)` of a scheme `A` over `K`: the `K`-morphisms `Spec L ⟶ A`,
written additively. For a commutative group object `A` its group law is the one induced by `A`
(`GeomPoints.instAddCommGroup`). -/
@[expose]
def GeomPoints : Type u :=
  Additive (specOver K L ⟶ A)

namespace GeomPoints

/-- The identification of a geometric point with the underlying morphism `Spec L ⟶ A`. -/
@[expose]
def toHom : GeomPoints K L A ≃ (specOver K L ⟶ A) :=
  Additive.toMul

variable {K L A}

/-- The action of `σ : L ≃ₐ[K] L` on `A(L)`: precomposition with `Spec σ`. -/
noncomputable instance instSMul : SMul (L ≃ₐ[K] L) (GeomPoints K L A) :=
  ⟨fun σ P => (toHom K L A).symm (specAut K L σ ≫ toHom K L A P)⟩

/-- `σ • P = Spec σ ≫ P`. -/
theorem toHom_smul (σ : L ≃ₐ[K] L) (P : GeomPoints K L A) :
    toHom K L A (σ • P) = specAut K L σ ≫ toHom K L A P :=
  (toHom K L A).apply_symm_apply _

/-- The identity of `L` acts trivially. -/
theorem one_smul_eq (P : GeomPoints K L A) : (1 : L ≃ₐ[K] L) • P = P :=
  (toHom K L A).injective (by rw [toHom_smul, specAut_one, Category.id_comp])

/-- The action is a left action: `(σ * τ) • P = σ • τ • P`. -/
theorem mul_smul_eq (σ τ : L ≃ₐ[K] L) (P : GeomPoints K L A) :
    (σ * τ) • P = σ • τ • P :=
  (toHom K L A).injective (by
    rw [toHom_smul, toHom_smul, toHom_smul, specAut_mul, Category.assoc])

variable [GrpObj A] [IsCommMonObj A]

/-- The commutative group structure on `A(L)` induced by the group object structure of `A`
(`CategoryTheory.Hom.commGroup`), written additively. -/
noncomputable instance instAddCommGroup : AddCommGroup (GeomPoints K L A) :=
  @Additive.addCommGroup _ CategoryTheory.Hom.commGroup

/-- Addition of points is the product in the hom-group `Hom(Spec L, A)`. -/
theorem toHom_add (P Q : GeomPoints K L A) :
    toHom K L A (P + Q) = toHom K L A P * toHom K L A Q :=
  rfl

/-- Addition of points is `lift P Q ≫ μ`, the multiplication of the group object `A`. -/
theorem toHom_add_eq_lift (P Q : GeomPoints K L A) :
    toHom K L A (P + Q) = lift (toHom K L A P) (toHom K L A Q) ≫ MonObj.mul :=
  rfl

/-- The zero point is the unit of the hom-group `Hom(Spec L, A)`. -/
theorem toHom_zero : toHom K L A (0 : GeomPoints K L A) = 1 :=
  rfl

/-- The zero point is `Spec L ⟶ 𝟙_ ⟶ A`, the unit of the group object `A`. -/
theorem toHom_zero_eq : toHom K L A (0 : GeomPoints K L A) = toUnit _ ≫ MonObj.one :=
  rfl

/-- Negation of points is inversion in the hom-group `Hom(Spec L, A)`. -/
theorem toHom_neg (P : GeomPoints K L A) : toHom K L A (-P) = (toHom K L A P)⁻¹ :=
  rfl

/-- `σ` fixes the zero point. -/
theorem smul_zero_eq (σ : L ≃ₐ[K] L) : σ • (0 : GeomPoints K L A) = 0 :=
  (toHom K L A).injective (by rw [toHom_smul, toHom_zero, MonObj.comp_one])

/-- `σ` acts additively. -/
theorem smul_add_eq (σ : L ≃ₐ[K] L) (P Q : GeomPoints K L A) :
    σ • (P + Q) = σ • P + σ • Q :=
  (toHom K L A).injective (by
    rw [toHom_smul, toHom_add, toHom_add, toHom_smul, toHom_smul, MonObj.comp_mul])

/-- The Galois group `L ≃ₐ[K] L` acts on `A(L)` (on the left, by precomposition with `Spec σ`)
by group automorphisms. -/
noncomputable instance instDistribMulAction :
    DistribMulAction (L ≃ₐ[K] L) (GeomPoints K L A) where
  toSMul := instSMul
  one_smul := one_smul_eq
  mul_smul := mul_smul_eq
  smul_zero := smul_zero_eq
  smul_add := smul_add_eq

/-- The action of `σ` commutes with multiplication by an integer. -/
theorem smul_zsmul_comm (σ : L ≃ₐ[K] L) (n : ℤ) (P : GeomPoints K L A) :
    σ • (n • P) = n • (σ • P) :=
  map_zsmul (DistribSMul.toAddMonoidHom (GeomPoints K L A) σ) n P

/-- The action of `σ` commutes with multiplication by a natural number. -/
theorem smul_nsmul_comm (σ : L ≃ₐ[K] L) (n : ℕ) (P : GeomPoints K L A) :
    σ • (n • P) = n • (σ • P) :=
  map_nsmul (DistribSMul.toAddMonoidHom (GeomPoints K L A) σ) n P

/-- The `n`-torsion subgroup `A(L)[n]` is stable under the Galois action. -/
theorem smul_mem_torsionBy (σ : L ≃ₐ[K] L) {n : ℤ} {P : GeomPoints K L A}
    (hP : P ∈ AddSubgroup.torsionBy (GeomPoints K L A) n) :
    σ • P ∈ AddSubgroup.torsionBy (GeomPoints K L A) n :=
  (Submodule.mem_torsionBy_iff _ _).2 (by
    rw [← smul_zsmul_comm, (Submodule.mem_torsionBy_iff _ _).1 hP, smul_zero])

/-- The Galois action on the `n`-torsion subgroup `A(L)[n]`, by group automorphisms. -/
noncomputable instance instDistribMulActionTorsionBy (n : ℤ) :
    DistribMulAction (L ≃ₐ[K] L) (AddSubgroup.torsionBy (GeomPoints K L A) n) where
  smul σ P := ⟨σ • (P : GeomPoints K L A), smul_mem_torsionBy σ P.2⟩
  one_smul P := Subtype.ext (one_smul _ (P : GeomPoints K L A))
  mul_smul σ τ P := Subtype.ext (mul_smul σ τ (P : GeomPoints K L A))
  smul_zero σ := Subtype.ext (smul_zero σ : σ • (0 : GeomPoints K L A) = 0)
  smul_add σ P Q := Subtype.ext (smul_add σ (P : GeomPoints K L A) Q)

/-- The action on `A(L)[n]` is the restriction of the action on `A(L)`. -/
@[simp]
theorem coe_smul_torsionBy (σ : L ≃ₐ[K] L) {n : ℤ}
    (P : AddSubgroup.torsionBy (GeomPoints K L A) n) :
    ((σ • P : AddSubgroup.torsionBy (GeomPoints K L A) n) : GeomPoints K L A) =
      σ • (P : GeomPoints K L A) :=
  rfl

variable (K L A) in
/-- Multiplication by `ℓ`, as a map `A(L)[ℓ^(n+1)] →+ A(L)[ℓ^n]`. -/
@[expose]
noncomputable def torsionMulMap (ℓ n : ℕ) :
    AddSubgroup.torsionBy (GeomPoints K L A) ((ℓ ^ (n + 1) : ℕ) : ℤ) →+
      AddSubgroup.torsionBy (GeomPoints K L A) ((ℓ ^ n : ℕ) : ℤ) where
  toFun P := ⟨ℓ • (P : GeomPoints K L A), AddSubgroup.torsionBy.nsmul_iff.2 (by
    rw [← mul_nsmul', ← pow_succ]
    exact AddSubgroup.torsionBy.nsmul_iff.1 P.2)⟩
  map_zero' := Subtype.ext (nsmul_zero ℓ : ℓ • (0 : GeomPoints K L A) = 0)
  map_add' P Q := Subtype.ext (nsmul_add (P : GeomPoints K L A) Q ℓ)

/-- `torsionMulMap K L A ℓ n P = ℓ • P` on underlying points. -/
@[simp]
theorem coe_torsionMulMap (ℓ n : ℕ)
    (P : AddSubgroup.torsionBy (GeomPoints K L A) ((ℓ ^ (n + 1) : ℕ) : ℤ)) :
    (torsionMulMap K L A ℓ n P : GeomPoints K L A) = ℓ • (P : GeomPoints K L A) :=
  rfl

/-- The multiplication-by-`ℓ` maps `A(L)[ℓ^(n+1)] → A(L)[ℓ^n]` are Galois-equivariant. -/
theorem torsionMulMap_smul (ℓ n : ℕ) (σ : L ≃ₐ[K] L)
    (P : AddSubgroup.torsionBy (GeomPoints K L A) ((ℓ ^ (n + 1) : ℕ) : ℤ)) :
    torsionMulMap K L A ℓ n (σ • P) = σ • torsionMulMap K L A ℓ n P :=
  Subtype.ext (smul_nsmul_comm σ ℓ (P : GeomPoints K L A)).symm

end GeomPoints

end GroupScheme

end ArithmeticOfJacobiPolynomials
