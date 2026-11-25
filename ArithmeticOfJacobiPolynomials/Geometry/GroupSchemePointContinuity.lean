/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.GroupSchemeGeometricPoints
public import ArithmeticOfJacobiPolynomials.Algebra.GaloisAlgHomAction
public import ArithmeticOfJacobiPolynomials.Algebra.TateGeometricAction
public import ArithmeticOfJacobiPolynomials.Algebra.TateTopology
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Open stabilizers of the Galois action on geometric points

Let `K` be a field, `L` an algebraic extension of `K` (for instance `AlgebraicClosure K`) and
`X` a scheme locally of finite type over `K`. The group `L ≃ₐ[K] L` acts on the `L`-points
`Spec L ⟶ X` over `K` by precomposition with `Spec σ` (the orientation of
`ArithmeticOfJacobiPolynomials.GroupScheme.GeomPoints`). We show that every stabilizer is open in
the Krull
topology.

* `ArithmeticOfJacobiPolynomials.GroupScheme.pointRingHom P` is the ring map `Γ(X, ⊤) → L` on
global sections
  of a point `P : Spec L ⟶ X`. Precomposing `P` with `Spec s` postcomposes `pointRingHom P` with
  `s` (`pointRingHom_specMap_comp`), and for affine `X` the point is determined by its ring map
  (`pointRingHom_injective`). Hence for affine `X`, `Spec σ ≫ P = P` iff `σ` fixes every value of
  `pointRingHom P` (`specMap_comp_eq_self_iff`).
* `ArithmeticOfJacobiPolynomials.GroupScheme.isOpen_setOf_specMap_comp_eq_of_isAffine`: the affine
case, from
  `ArithmeticOfJacobiPolynomials.GaloisAlgHom.isOpen_setOf_forall_apply_eq_of_ringHom`.
* `ArithmeticOfJacobiPolynomials.GroupScheme.isOpen_setOf_specMap_comp_eq`: the general case (`X`
locally of finite
  type over `K`, no affineness or quasi-compactness): `Spec L` has a single point, so `P` factors
  through an affine open `Spec R ⟶ X`, an open immersion and hence a monomorphism.
* `ArithmeticOfJacobiPolynomials.GroupScheme.GeomPoints.isOpen_stabilizer`: for `A : Over (Spec K)`
a commutative
  group object with `A.hom` locally of finite type, the stabilizer of every point of `A(L)` is
  open; `GeomPoints.isOpen_stabilizer_torsionBy` is the same for the points of `A(L)[n]`.
* `ArithmeticOfJacobiPolynomials.GroupScheme.continuous_galoisRepresentation`: hence the Galois
representation
  `galoisRepresentation ℓ K L A` on the Tate module `T_ℓ(A(L))` is continuous, as a map
  `(L ≃ₐ[K] L) × T_ℓ(A(L)) → T_ℓ(A(L))` (Krull topology, inverse-limit topology).
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace ArithmeticOfJacobiPolynomials

open Stacks.AbelianGroup

namespace GroupScheme

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]

/-- The ring map `Γ(X, ⊤) → L` on global sections of a point `P : Spec L ⟶ X`. -/
noncomputable def pointRingHom {X : Scheme.{u}} (P : Spec (.of L) ⟶ X) :
    Γ(X, ⊤) ⟶ CommRingCat.of L :=
  P.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom

/-- Precomposition with `Spec s` is postcomposition of the ring map with `s`. -/
theorem pointRingHom_specMap_comp {X : Scheme.{u}} (s : CommRingCat.of L ⟶ CommRingCat.of L)
    (P : Spec (.of L) ⟶ X) :
    pointRingHom (Spec.map s ≫ P) = pointRingHom P ≫ s := by
  rw [pointRingHom, pointRingHom, Scheme.Hom.comp_appTop, Category.assoc,
    Scheme.ΓSpecIso_naturality, Category.assoc]

/-- A point of an affine scheme is determined by its ring map on global sections. -/
theorem pointRingHom_injective {X : Scheme.{u}} [IsAffine X] {P Q : Spec (.of L) ⟶ X}
    (h : pointRingHom P = pointRingHom Q) : P = Q :=
  ext_of_isAffine ((cancel_mono (Scheme.ΓSpecIso (.of L)).hom).1 h)

/-- For affine `X`, `Spec s ≫ P = P` iff `s` fixes every value of the ring map of `P`. -/
theorem specMap_comp_eq_self_iff {X : Scheme.{u}} [IsAffine X] (s : L →+* L)
    (P : Spec (.of L) ⟶ X) :
    Spec.map (CommRingCat.ofHom s) ≫ P = P ↔
      ∀ x, s ((pointRingHom P).hom x) = (pointRingHom P).hom x := by
  constructor
  · intro h x
    have h' : (pointRingHom (Spec.map (CommRingCat.ofHom s) ≫ P)).hom x =
        (pointRingHom P).hom x := by rw [h]
    rw [pointRingHom_specMap_comp] at h'
    exact h'
  · intro h
    apply pointRingHom_injective
    rw [pointRingHom_specMap_comp]
    ext x
    exact h x

/-- The ring map of a `K`-point is compatible with the structure maps:
`K ≅ Γ(Spec K) → Γ(X) → L` is `algebraMap K L`. -/
theorem ΓSpecIso_inv_comp_pointRingHom {X : Scheme.{u}} (g : X ⟶ Spec (.of K))
    (P : Spec (.of L) ⟶ X) (hP : P ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    (Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop ≫ pointRingHom P =
      CommRingCat.ofHom (algebraMap K L) := by
  rw [pointRingHom, ← Category.assoc g.appTop, ← Scheme.Hom.comp_appTop, hP,
    Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

/-- Affine case: for an affine scheme `X` locally of finite type over `K` (structure map `g`) and
a `K`-point `P : Spec L ⟶ X`, the automorphisms `σ` with `Spec σ ≫ P = P` form an open subset
of `L ≃ₐ[K] L`. -/
theorem isOpen_setOf_specMap_comp_eq_of_isAffine [Algebra.IsAlgebraic K L] {X : Scheme.{u}}
    [IsAffine X] (g : X ⟶ Spec (.of K)) [LocallyOfFiniteType g] (P : Spec (.of L) ⟶ X)
    (hP : P ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    IsOpen {σ : L ≃ₐ[K] L | Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫ P = P} := by
  have hg : g.appTop.hom.FiniteType :=
    HasRingHomProperty.appTop @LocallyOfFiniteType g inferInstance
  have hsurj : Function.Surjective (Scheme.ΓSpecIso (.of K)).inv.hom := fun y =>
    ⟨(Scheme.ΓSpecIso (.of K)).hom.hom y,
      congrArg (fun f => CommRingCat.Hom.hom f y) (Scheme.ΓSpecIso (.of K)).hom_inv_id⟩
  have hk : ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop).hom.FiniteType := by
    rw [CommRingCat.hom_comp]
    exact hg.comp (RingHom.FiniteType.of_surjective _ hsurj)
  have hf : (pointRingHom P).hom.comp ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop).hom =
      algebraMap K L := by
    rw [← CommRingCat.hom_comp, Category.assoc, ΓSpecIso_inv_comp_pointRingHom g P hP,
      CommRingCat.hom_ofHom]
  have h := GaloisAlgHom.isOpen_setOf_forall_apply_eq_of_ringHom (K := K) (L := L) _ hk
    (pointRingHom P).hom hf
  have e : {σ : L ≃ₐ[K] L | Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫ P = P} =
      {σ : L ≃ₐ[K] L | ∀ x, σ ((pointRingHom P).hom x) = (pointRingHom P).hom x} :=
    Set.ext fun σ => specMap_comp_eq_self_iff (σ : L →+* L) P
  rw [e]
  exact h

/-- General case: for a scheme `X` locally of finite type over `K` (structure map `g`) and a
`K`-point `P : Spec L ⟶ X`, the automorphisms `σ` with `Spec σ ≫ P = P` form an open subset
of `L ≃ₐ[K] L`. The point factors through an affine open of `X`. -/
theorem isOpen_setOf_specMap_comp_eq [Algebra.IsAlgebraic K L] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of K)) [LocallyOfFiniteType g] (P : Spec (.of L) ⟶ X)
    (hP : P ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    IsOpen {σ : L ≃ₐ[K] L | Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫ P = P} := by
  obtain ⟨R, i, hi, hx, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := P (default : Spec (.of L))) (U := ⊤) (by simp)
  have hrange : Set.range P ⊆ Set.range i := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z default]
    exact hx
  obtain ⟨P', hfac⟩ : ∃ P' : Spec (.of L) ⟶ Spec R, P' ≫ i = P :=
    ⟨_, IsOpenImmersion.lift_fac (f := i) (g := P) hrange⟩
  have hP' : P' ≫ (i ≫ g) = Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    rw [← Category.assoc, hfac, hP]
  have h := isOpen_setOf_specMap_comp_eq_of_isAffine (i ≫ g) P' hP'
  have e : {σ : L ≃ₐ[K] L | Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫ P = P} =
      {σ : L ≃ₐ[K] L | Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫ P' = P'} := by
    ext σ
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hσ
      apply (cancel_mono i).1
      rw [Category.assoc, hfac, hσ]
    · intro hσ
      rw [← hfac, ← Category.assoc, hσ]
  rw [e]
  exact h

namespace GeomPoints

variable {A : Over (Spec (.of K))}

/-- `σ` fixes a geometric point `P` iff `Spec σ ≫ P = P` on underlying morphisms of schemes. -/
theorem smul_eq_self_iff (σ : L ≃ₐ[K] L) (P : GeomPoints K L A) :
    σ • P = P ↔ Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫ (toHom K L A P).left =
      (toHom K L A P).left := by
  rw [← (toHom K L A).injective.eq_iff, toHom_smul]
  constructor
  · intro h
    rw [← specAut_left, ← Over.comp_left, h]
  · intro h
    apply Over.OverMorphism.ext
    rw [Over.comp_left, specAut_left, h]

/-- For `A` locally of finite type over `K` and `L/K` algebraic, the set of `σ` fixing a
geometric point `P ∈ A(L)` is open (no group structure on `A` is needed). -/
theorem isOpen_setOf_smul_eq [Algebra.IsAlgebraic K L] [LocallyOfFiniteType A.hom]
    (P : GeomPoints K L A) :
    IsOpen {σ : L ≃ₐ[K] L | σ • P = P} := by
  have h := isOpen_setOf_specMap_comp_eq A.hom (toHom K L A P).left (Over.w (toHom K L A P))
  have e : {σ : L ≃ₐ[K] L | σ • P = P} =
      {σ : L ≃ₐ[K] L | Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫ (toHom K L A P).left =
        (toHom K L A P).left} :=
    Set.ext fun σ => smul_eq_self_iff σ P
  rw [e]
  exact h

variable [GrpObj A] [IsCommMonObj A]

/-- **Open stabilizers.** For a commutative group scheme `A` locally of finite type over `K` and
an algebraic extension `L/K`, the stabilizer of every geometric point `P ∈ A(L)` is open in the
Krull topology of `L ≃ₐ[K] L`; that is, the Galois action on `A(L)` is continuous for the
discrete topology on `A(L)`. -/
theorem isOpen_stabilizer [Algebra.IsAlgebraic K L] [LocallyOfFiniteType A.hom]
    (P : GeomPoints K L A) :
    IsOpen (MulAction.stabilizer (L ≃ₐ[K] L) P : Set (L ≃ₐ[K] L)) := by
  have e : (MulAction.stabilizer (L ≃ₐ[K] L) P : Set (L ≃ₐ[K] L)) =
      {σ : L ≃ₐ[K] L | σ • P = P} :=
    Set.ext fun σ => MulAction.mem_stabilizer_iff
  rw [e]
  exact isOpen_setOf_smul_eq P

/-- The stabilizer of every point of the torsion subgroup `A(L)[n]` is open. -/
theorem isOpen_stabilizer_torsionBy [Algebra.IsAlgebraic K L] [LocallyOfFiniteType A.hom]
    (n : ℤ) (P : AddSubgroup.torsionBy (GeomPoints K L A) n) :
    IsOpen (MulAction.stabilizer (L ≃ₐ[K] L) P : Set (L ≃ₐ[K] L)) := by
  have e : (MulAction.stabilizer (L ≃ₐ[K] L) P : Set (L ≃ₐ[K] L)) =
      (MulAction.stabilizer (L ≃ₐ[K] L) (P : GeomPoints K L A) : Set (L ≃ₐ[K] L)) := by
    ext σ
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      rw [← coe_smul_torsionBy, h]
    · intro h
      exact Subtype.ext ((coe_smul_torsionBy σ P).trans h)
  rw [e]
  exact isOpen_stabilizer (P : GeomPoints K L A)

/-- The hypothesis form used for continuity of Tate-module representations: every point of
`A(L)` killed by `ℓ ^ n` has open stabilizer. -/
theorem isOpen_stabilizer_of_pow_smul_eq_zero [Algebra.IsAlgebraic K L]
    [LocallyOfFiniteType A.hom] (ℓ : ℕ) :
    ∀ (n : ℕ) (P : GeomPoints K L A), ℓ ^ n • P = 0 →
      IsOpen (MulAction.stabilizer (L ≃ₐ[K] L) P : Set (L ≃ₐ[K] L)) :=
  fun _ P _ => isOpen_stabilizer P

end GeomPoints

variable {A : Over (Spec (.of K))} [GrpObj A] [IsCommMonObj A]

/-- **Continuity of the Galois representation on the Tate module.** For a commutative group
scheme `A` locally of finite type over `K`, an algebraic extension `L/K` and a prime `ℓ`, the
action map `(σ, x) ↦ ρ(σ) x` of `L ≃ₐ[K] L` (Krull topology) on `T_ℓ(A(L))` (inverse-limit
topology) is continuous. -/
theorem continuous_galoisRepresentation [Algebra.IsAlgebraic K L] [LocallyOfFiniteType A.hom]
    (ℓ : ℕ) [Fact ℓ.Prime] :
    Continuous fun p : (L ≃ₐ[K] L) × tateModule (GeomPoints K L A) ℓ =>
      galoisRepresentation ℓ K L A p.1 p.2 :=
  tateModule.continuous_representation (GeomPoints.isOpen_stabilizer_of_pow_smul_eq_zero ℓ)

end GroupScheme

end ArithmeticOfJacobiPolynomials
