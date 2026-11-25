/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.GroupObjectEndTate
public import ArithmeticOfJacobiPolynomials.Algebra.TateGeometricAction
public import ArithmeticOfJacobiPolynomials.Algebra.TatePairingPerfect
public import ArithmeticOfJacobiPolynomials.Algebra.TateRational
public import ArithmeticOfJacobiPolynomials.Geometry.AbelianVariety
public import ArithmeticOfJacobiPolynomials.Geometry.GroupSchemeBaseChange
public import ArithmeticOfJacobiPolynomials.Geometry.GroupSchemePointContinuity
public import ArithmeticOfJacobiPolynomials.Algebra.TateRationalTopology
public import ArithmeticOfJacobiPolynomials.Geometry.Jacobian.Basic
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.FromCube
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowSurjective

/-!
# The Tate module of an abelian variety: freeness, finiteness and rank `2 dim`

Let `K` be a field, `A` an abelian variety over `K` (`A : Over (Spec K)` with `[GrpObj A]`,
`[IsCommMonObj A]`, `AlgebraicGeometry.IsAbelianVariety K A`), `L` an algebraically closed
extension of `K` (e.g. `AlgebraicClosure K`) and `ℓ` a prime with `(ℓ : L) ≠ 0`. The Tate module
considered here is the Stacks module `Stacks.AbelianGroup.tateModule` applied to the
group `A(L) = GeomPoints K L A` of `L`-points of the group scheme `A`
(`ArithmeticOfJacobiPolynomials.GroupScheme.GeomPoints`, whose group law is the one of the group
object `A`). It carries the `ℤ_ℓ`-module structure of `tateModule`, the Galois action
`ArithmeticOfJacobiPolynomials.GroupScheme.galoisRepresentation` of `L ≃ₐ[K] L` and the action of
`GrpObjEnd A` (`ArithmeticOfJacobiPolynomials.tateEndAction`), all by `ℤ_ℓ`-linear maps of the same
module.

## What is proved, and from which Stacks results

Base change `A_L` of `A` to `L` is an abelian variety over the algebraically closed field `L`,
with `A_L(L) ≅ A(L)` (`ArithmeticOfJacobiPolynomials.GroupScheme.baseChangePointsEquiv`) and
`A_L(L) = Hom(𝟙_, A_L)` (`GroupScheme.selfPointsEquiv`). Then

* `ArithmeticOfJacobiPolynomials.GroupScheme.geomPoints_ell_divisible`: `A(L)` is `ℓ`-divisible.
This is
  `Stacks.Groupoids.exists_nsmul_eq_of_isUnit` ([Stacks, Tag 03RP], clause (4); multiplication by
  `ℓ` is étale because `ℓ` is invertible in `L`).
* `ArithmeticOfJacobiPolynomials.GroupScheme.nonempty_torsionEquiv_geomPoints`:
  `A(L)[ℓ^n] ≃+ (ℤ/ℓ^n)^{2 g}` with `g = dim A_L`. This is
  `Stacks.Groupoids.nonempty_torsionBy_addEquiv_pi_zmod` ([Stacks, Tag 03RP] part (7), proved from
  the cube relation, so the degree `d^{2g}` of multiplication by `d` is not an input).
* `ArithmeticOfJacobiPolynomials.GroupScheme.module_free_tateModule_geomPoints`,
  `module_finite_tateModule_geomPoints`, `finrank_tateModule_geomPoints`: `T_ℓ(A(L))` is a free
  finite `ℤ_ℓ`-module of rank `2 * dim A_L` (generic `Stacks.AbelianGroup.module_free_tateModule`
  etc. applied to the two facts above), and `finrank_rationalTate_geomPoints`:
  `dim_{ℚ_ℓ} V_ℓ(A(L)) = 2 * dim A_L`.

The dimension is the geometric dimension `geomDim L A := abelianVarietyDimension A_L`
(`Stacks.Groupoids.abelianVarietyDimension`, the Krull dimension of the scheme `A_L`). Nothing
here relates `geomDim` to the genus of a curve; that is the separate result `dim J = genus`
(Stacks Tag 0BA0 over an algebraically closed field).

For a Jacobian `IsJacobianOf B hX hk f hdim J`
(`ArithmeticOfJacobiPolynomials.Jacobian.IsJacobianOf`), `J.X` is
an abelian variety (a structure field), so everything above applies to `T_ℓ(J)`: see
`ArithmeticOfJacobiPolynomials.Jacobian.IsJacobianOf.finrank_tateModule`.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry PadicInt
open scoped CategoryTheory.MonObj

universe u

namespace ArithmeticOfJacobiPolynomials

open Stacks.AbelianGroup

/-! ### Generic transport along an additive equivalence -/

section Generic

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- Divisibility transfers along an additive equivalence. -/
theorem divisible_of_addEquiv (e : M ≃+ N) {ℓ : ℕ} (h : ∀ x : N, ∃ y, ℓ • y = x) :
    ∀ x : M, ∃ y, ℓ • y = x := fun x => by
  obtain ⟨y, hy⟩ := h (e x)
  exact ⟨e.symm y, by rw [← map_nsmul, hy, e.symm_apply_apply]⟩

/-- The two spellings `AddSubgroup.torsionBy M m` and `Submodule.torsionBy ℤ M m` of the
`m`-torsion subgroup. -/
def torsionBySubmoduleEquiv (M : Type*) [AddCommGroup M] (m : ℤ) :
    AddSubgroup.torsionBy M m ≃+ Submodule.torsionBy ℤ M m :=
  AddEquiv.refl _

/-- `m`-torsion structure transfers along an additive equivalence, from the
`Submodule.torsionBy ℤ` spelling to the `AddSubgroup.torsionBy` spelling. -/
theorem nonempty_torsionBy_addEquiv_of_addEquiv (e : M ≃+ N) (m : ℤ) {P : Type*}
    [AddCommGroup P] (h : Nonempty (Submodule.torsionBy ℤ N m ≃+ P)) :
    Nonempty (AddSubgroup.torsionBy M m ≃+ P) := by
  obtain ⟨φ⟩ := h
  exact ⟨((torsionAddEquiv e m).trans (torsionBySubmoduleEquiv N m)).trans φ⟩

end Generic

/-! ### Rational points of the base change -/

namespace GroupScheme

variable (L : Type u) [Field L]

/-- `Spec L`, as an object over itself, is the unit of `Over (Spec L)`. -/
noncomputable def specOverSelfIso : specOver L L ≅ 𝟙_ (Over (Spec (.of L))) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ 𝟙 _ = Spec.map (CommRingCat.ofHom (algebraMap L L))
    rw [Category.id_comp]
    have : CommRingCat.ofHom (algebraMap L L) = 𝟙 (CommRingCat.of L) := by
      ext x
      rfl
    rw [this, Spec.map_id])

variable (B : Over (Spec (.of L))) [GrpObj B] [IsCommMonObj B]

attribute [local instance] Hom.commGroup

/-- **Points over the base field are the rational points.** The additive group `B(L)` of
`GeomPoints L L B` (`L`-morphisms `Spec L ⟶ B`) is the group of morphisms `𝟙_ ⟶ B` from the unit of
`Over (Spec L)`, written additively. -/
@[expose]
noncomputable def selfPointsEquiv :
    GeomPoints L L B ≃+ Additive (𝟙_ (Over (Spec (.of L))) ⟶ B) where
  toFun P := Additive.ofMul ((specOverSelfIso L).inv ≫ GeomPoints.toHom L L B P)
  invFun Q := (GeomPoints.toHom L L B).symm ((specOverSelfIso L).hom ≫ Additive.toMul Q)
  left_inv P := by
    apply (GeomPoints.toHom L L B).injective
    simp
  right_inv Q := by
    apply Additive.toMul.injective
    simp
  map_add' P Q := by
    change Additive.ofMul ((specOverSelfIso L).inv ≫ GeomPoints.toHom L L B (P + Q)) = _
    rw [GeomPoints.toHom_add, MonObj.comp_mul]
    rfl

end GroupScheme

/-! ### The geometric dimension and the Tate module of `A(L)` -/

namespace GroupScheme

variable {K : Type u} [Field K] (L : Type u) [Field L] [Algebra K L]
  (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]

/-- **The geometric dimension** of `A` along `L`: the dimension of the abelian variety `A_L`
over `L` (`Stacks.Groupoids.abelianVarietyDimension`). -/
@[expose]
noncomputable def geomDim : ℕ :=
  Stacks.Groupoids.abelianVarietyDimension (baseChange L A)

variable [IsAlgClosed L]

attribute [local instance] Hom.commGroup

/-- The additive isomorphism `A(L) ≃ A_L(L) = Hom(𝟙_, A_L)` from the base change. -/
@[expose]
noncomputable def geomPointsEquivUnit :
    GeomPoints K L A ≃+ Additive (𝟙_ (Over (Spec (.of L))) ⟶ baseChange L A) :=
  (baseChangePointsEquiv L A L).symm.trans (selfPointsEquiv L (baseChange L A))

variable [IsAbelianVariety K A] {ℓ : ℕ}

omit [IsCommMonObj A] [IsAlgClosed L] in
/-- `A_L` is an abelian variety over `L`. -/
theorem isAbelianVariety_baseChange : IsAbelianVariety L (baseChange L A) :=
  IsAbelianVariety.baseChange (A := A) L

/-- **`A(L)` is `ℓ`-divisible** when `(ℓ : L) ≠ 0` ([Stacks, Tag 03RP], clause (4)). -/
theorem geomPoints_ell_divisible (hℓ : (ℓ : L) ≠ 0) :
    ∀ x : GeomPoints K L A, ∃ y, ℓ • y = x := by
  have := isAbelianVariety_baseChange L A
  refine divisible_of_addEquiv (geomPointsEquivUnit L A) fun x => ?_
  exact Stacks.Groupoids.exists_nsmul_eq_of_isUnit (baseChange L A) ℓ (hℓ.isUnit) x

/-- **The finite-level torsion of `A(L)`**: for `(ℓ : L) ≠ 0`, `A(L)[ℓ^n] ≃+ (ℤ/ℓ^n)^{2 g}`,
`g = geomDim L A` ([Stacks, Tag 03RP], part (7)). -/
theorem nonempty_torsionEquiv_geomPoints (hℓ : (ℓ : L) ≠ 0) (n : ℕ) :
    Nonempty (AddSubgroup.torsionBy (GeomPoints K L A) ((ℓ ^ n : ℕ) : ℤ) ≃+
      (Fin (2 * geomDim L A) → ZMod (ℓ ^ n))) := by
  have := isAbelianVariety_baseChange L A
  refine nonempty_torsionBy_addEquiv_of_addEquiv (geomPointsEquivUnit L A) _ ?_
  have hn : IsUnit ((ℓ ^ n : ℕ) : L) :=
    (natCast_pow_ne_zero_of_natCast_ne_zero (L := L) hℓ n).isUnit
  exact Stacks.Groupoids.nonempty_torsionBy_addEquiv_pi_zmod (baseChange L A) (ℓ ^ n)
    (Nat.one_le_pow _ _ (Nat.pos_of_ne_zero fun h => by simp [h] at hℓ)) hn

variable [Fact ℓ.Prime]

/-- **`T_ℓ(A(L))` is a free `ℤ_ℓ`-module.** -/
theorem module_free_tateModule_geomPoints (hℓ : (ℓ : L) ≠ 0) :
    Module.Free ℤ_[ℓ] (tateModule (GeomPoints K L A) ℓ) :=
  module_free_tateModule (geomPoints_ell_divisible L A hℓ)
    (nonempty_torsionEquiv_geomPoints L A hℓ)

/-- **`T_ℓ(A(L))` is a finitely generated `ℤ_ℓ`-module.** -/
theorem module_finite_tateModule_geomPoints (hℓ : (ℓ : L) ≠ 0) :
    Module.Finite ℤ_[ℓ] (tateModule (GeomPoints K L A) ℓ) :=
  module_finite_tateModule (geomPoints_ell_divisible L A hℓ)
    (nonempty_torsionEquiv_geomPoints L A hℓ)

/-- **Rank of the Tate module of an abelian variety**: `rank_{ℤ_ℓ} T_ℓ(A(L)) = 2 * dim A_L`. -/
theorem finrank_tateModule_geomPoints (hℓ : (ℓ : L) ≠ 0) :
    Module.finrank ℤ_[ℓ] (tateModule (GeomPoints K L A) ℓ) = 2 * geomDim L A :=
  finrank_tateModule (geomPoints_ell_divisible L A hℓ)
    (nonempty_torsionEquiv_geomPoints L A hℓ)

/-- **The rational Tate module is finite dimensional.** -/
theorem module_finite_rationalTate_geomPoints (hℓ : (ℓ : L) ≠ 0) :
    Module.Finite ℚ_[ℓ] (rationalTate ℓ (GeomPoints K L A)) :=
  module_finite_rationalTate (geomPoints_ell_divisible L A hℓ)
    (nonempty_torsionEquiv_geomPoints L A hℓ)

/-- **Rank of the rational Tate module**: `dim_{ℚ_ℓ} V_ℓ(A(L)) = 2 * dim A_L`. -/
theorem finrank_rationalTate_geomPoints (hℓ : (ℓ : L) ≠ 0) :
    Module.finrank ℚ_[ℓ] (rationalTate ℓ (GeomPoints K L A)) = 2 * geomDim L A :=
  finrank_rationalTate (geomPoints_ell_divisible L A hℓ)
    (nonempty_torsionEquiv_geomPoints L A hℓ)

/-- **Continuity of the Galois representation on the rational Tate module.** For an abelian
variety `A` over `K` and `L/K` algebraically closed and algebraic (that is, `L = K̄`), the action
map `Aut(L/K) × V_ℓ(A(L)) → V_ℓ(A(L))` is continuous for the Krull topology and the module
topology on `V_ℓ`. Stabilizers of `A(L)[ℓ^n]` are open (`GeomPoints.isOpen_stabilizer`), and
`V_ℓ(A(L))` is finite free by the above. -/
theorem continuous_rationalTate_representation_geomPoints [Algebra.IsAlgebraic K L]
    (hℓ : (ℓ : L) ≠ 0) :
    Continuous fun p : (L ≃ₐ[K] L) × rationalTate ℓ (GeomPoints K L A) =>
      rationalTate.representation ℓ (GeomPoints K L A) (L ≃ₐ[K] L) p.1 p.2 :=
  rationalTate.continuous_representation (geomPoints_ell_divisible L A hℓ)
    (nonempty_torsionEquiv_geomPoints L A hℓ) (L ≃ₐ[K] L)
    (GeomPoints.isOpen_stabilizer_of_pow_smul_eq_zero ℓ)

end GroupScheme

/-! ### Jacobians -/

namespace Jacobian

open GroupScheme

variable {k : Type u} [Field k] {B : BigFppfSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}
  {hk : B.Contains (Spec (.of k))} {f : B.obj hX ⟶ B.obj hk} [IsProper (B.inclusion.map f)]
  {hdim : topologicalKrullDim X ≤ 1} {J : Grp (Over (Spec (.of k)))} [IsCommMonObj J.X]
  (hJ : IsJacobianOf B hX hk f hdim J) (L : Type u) [Field L] [Algebra k L] [IsAlgClosed L]
  {ℓ : ℕ} [Fact ℓ.Prime]

include hJ

/-- **`T_ℓ(J)` is free over `ℤ_ℓ`** for the group of `L`-points of a Jacobian `J`
(`IsJacobianOf` includes that `J` is an abelian variety). -/
theorem IsJacobianOf.module_free_tateModule (hℓ : (ℓ : L) ≠ 0) :
    Module.Free ℤ_[ℓ] (tateModule (GeomPoints k L J.X) ℓ) :=
  haveI := hJ.isAbelianVariety
  module_free_tateModule_geomPoints L J.X hℓ

/-- **`T_ℓ(J)` is finitely generated over `ℤ_ℓ`.** -/
theorem IsJacobianOf.module_finite_tateModule (hℓ : (ℓ : L) ≠ 0) :
    Module.Finite ℤ_[ℓ] (tateModule (GeomPoints k L J.X) ℓ) :=
  haveI := hJ.isAbelianVariety
  module_finite_tateModule_geomPoints L J.X hℓ

/-- **Rank of `T_ℓ(J)`**: `2 * dim J_L`. -/
theorem IsJacobianOf.finrank_tateModule (hℓ : (ℓ : L) ≠ 0) :
    Module.finrank ℤ_[ℓ] (tateModule (GeomPoints k L J.X) ℓ) = 2 * geomDim L J.X :=
  haveI := hJ.isAbelianVariety
  finrank_tateModule_geomPoints L J.X hℓ

/-- **Rank of `V_ℓ(J)`**: `2 * dim J_L`. -/
theorem IsJacobianOf.finrank_rationalTate (hℓ : (ℓ : L) ≠ 0) :
    Module.finrank ℚ_[ℓ] (rationalTate ℓ (GeomPoints k L J.X)) = 2 * geomDim L J.X :=
  haveI := hJ.isAbelianVariety
  finrank_rationalTate_geomPoints L J.X hℓ

end Jacobian

end ArithmeticOfJacobiPolynomials
