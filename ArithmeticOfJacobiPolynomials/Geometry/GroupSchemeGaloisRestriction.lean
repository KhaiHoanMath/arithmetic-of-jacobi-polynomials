/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.NumberFieldGaloisAction
public import ArithmeticOfJacobiPolynomials.Geometry.GroupSchemePointContinuity

/-!
# Restricting the Galois action on points and Tate modules to `Gal(Ω/K)`

Let `Ω/k` be a field extension, `K` an intermediate field and `A` a commutative group scheme over
`k` (`A : Over (Spec k)` with `[GrpObj A] [IsCommMonObj A]`). The group `Gal(Ω/k)` acts on
`A(Ω) = GeomPoints k Ω A` and on `T_ℓ(A(Ω))` (`galoisRepresentation ℓ k Ω A`). Restricting along
`AlgEquiv.restrictScalarsHom k : Gal(Ω/K) →* Gal(Ω/k)` gives:

* `ArithmeticOfJacobiPolynomials.GroupScheme.restrictedDistribMulAction K A`: the action of `Ω
≃ₐ[K] Ω` on
  `A(Ω)` (a scoped instance, `open scoped
  ArithmeticOfJacobiPolynomials.GroupScheme.GaloisRestriction`);
* `ArithmeticOfJacobiPolynomials.GroupScheme.restrictedGaloisRepresentation ℓ K A`: the
representation of
  `Ω ≃ₐ[K] Ω` on `T_ℓ(A(Ω))`; it is the generic Tate-module representation of the restricted
  action (`restrictedGaloisRepresentation_eq_representation`), is computed componentwise
  (`restrictedGaloisRepresentation_seq`) and is compatible with the evaluations
  `T_ℓ(A(Ω)) → A(Ω)[ℓ^n]` (`tateReduction_restrictedGaloisRepresentation`);
* `continuous_restrictedGaloisRepresentation`: for `Ω/k` algebraic and `A` locally of finite
  type over `k`, the restricted action map `Gal(Ω/K) × T_ℓ(A(Ω)) → T_ℓ(A(Ω))` is continuous;
* the same for the restriction `fixingSubgroupGaloisRepresentation ℓ K A` to the fixing subgroup
  `K.fixingSubgroup ⊆ Gal(Ω/k)`, which corresponds to `restrictedGaloisRepresentation` under
  `IntermediateField.fixingSubgroupEquiv K` (`fixingSubgroupGaloisRepresentation_apply_eq`).

The section `Rat` records the case of a number field `K ⊆ ℚ̄ = AlgebraicClosure ℚ` and a group
scheme `A` locally of finite type over `ℚ`.

The base change `A_K` is not treated: here the points are those of `A` over `k`, with the
restricted Galois action.
-/

public section

open CategoryTheory AlgebraicGeometry PadicInt

universe u

namespace ArithmeticOfJacobiPolynomials

open Stacks.AbelianGroup

namespace GroupScheme

open NumberFieldGalois

section General

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] {Ω : Type u} [Field Ω] [Algebra k Ω]
  (K : IntermediateField k Ω) (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]

/-- The action of `Gal(Ω/K) = Ω ≃ₐ[K] Ω` on `A(Ω)`: `σ` acts as `σ` viewed in `Gal(Ω/k)`. It is a
scoped instance (`open scoped ArithmeticOfJacobiPolynomials.GroupScheme.GaloisRestriction`). -/
@[expose, reducible]
noncomputable def restrictedDistribMulAction :
    DistribMulAction (Ω ≃ₐ[K] Ω) (GeomPoints k Ω A) :=
  DistribMulAction.compHom (GeomPoints k Ω A) (AlgEquiv.restrictScalarsHom k)

namespace GaloisRestriction

attribute [scoped instance] ArithmeticOfJacobiPolynomials.GroupScheme.restrictedDistribMulAction

end GaloisRestriction

/-- The representation of `Gal(Ω/K)` on `T_ℓ(A(Ω))`: the restriction of
`galoisRepresentation ℓ k Ω A` along `Gal(Ω/K) →* Gal(Ω/k)`. -/
@[expose]
noncomputable def restrictedGaloisRepresentation :
    Representation ℤ_[ℓ] (Ω ≃ₐ[K] Ω) (tateModule (GeomPoints k Ω A) ℓ) :=
  (galoisRepresentation ℓ k Ω A).comp (AlgEquiv.restrictScalarsHom k)

/-- The representation of the fixing subgroup `K.fixingSubgroup ⊆ Gal(Ω/k)` on `T_ℓ(A(Ω))`: the
restriction of `galoisRepresentation ℓ k Ω A`. -/
@[expose]
noncomputable def fixingSubgroupGaloisRepresentation :
    Representation ℤ_[ℓ] K.fixingSubgroup (tateModule (GeomPoints k Ω A) ℓ) :=
  (galoisRepresentation ℓ k Ω A).comp K.fixingSubgroup.subtype

variable {ℓ K A}

/-- `σ ∈ Gal(Ω/K)` acts on `T_ℓ(A(Ω))` as `σ ∈ Gal(Ω/k)`. -/
theorem restrictedGaloisRepresentation_apply (σ : Ω ≃ₐ[K] Ω) :
    restrictedGaloisRepresentation ℓ K A σ =
      galoisRepresentation ℓ k Ω A (AlgEquiv.restrictScalarsHom k σ) :=
  MonoidHom.comp_apply _ _ σ

/-- The `n`-th component of `σ • x` is `σ • x n` (with `σ` viewed in `Gal(Ω/k)`). -/
@[simp]
theorem restrictedGaloisRepresentation_seq (σ : Ω ≃ₐ[K] Ω)
    (x : tateModule (GeomPoints k Ω A) ℓ) (n : ℕ) :
    ((restrictedGaloisRepresentation ℓ K A σ x : tateModule (GeomPoints k Ω A) ℓ) :
        ℕ → GeomPoints k Ω A) n =
      AlgEquiv.restrictScalarsHom k σ • (x : ℕ → GeomPoints k Ω A) n := by
  rw [restrictedGaloisRepresentation_apply, galoisRepresentation_seq]

/-- **Compatibility with the finite levels.** The restricted action on `T_ℓ(A(Ω))` is compatible
with the evaluations `T_ℓ(A(Ω)) → A(Ω)[ℓ^n]` and the Galois action on `A(Ω)[ℓ^n]`. -/
theorem tateReduction_restrictedGaloisRepresentation (n : ℕ) (σ : Ω ≃ₐ[K] Ω)
    (x : tateModule (GeomPoints k Ω A) ℓ) :
    tateReduction ℓ n (restrictedGaloisRepresentation ℓ K A σ x) =
      AlgEquiv.restrictScalarsHom k σ • tateReduction ℓ n x := by
  rw [restrictedGaloisRepresentation_apply, tateReduction_galoisRepresentation]

open scoped GaloisRestriction in
/-- With the scoped restricted action, `σ • P` is `σ` viewed in `Gal(Ω/k)` acting on `P`. -/
theorem restricted_smul_def (σ : Ω ≃ₐ[K] Ω) (P : GeomPoints k Ω A) :
    σ • P = AlgEquiv.restrictScalarsHom k σ • P :=
  rfl

open scoped GaloisRestriction in
/-- The restricted representation is the Tate-module representation
(`tateModule.representation`) of the restricted action of `Gal(Ω/K)` on `A(Ω)`. -/
theorem restrictedGaloisRepresentation_eq_representation :
    restrictedGaloisRepresentation ℓ K A =
      tateModule.representation ℓ (GeomPoints k Ω A) (Ω ≃ₐ[K] Ω) :=
  MonoidHom.ext fun σ => LinearMap.ext fun x => tateModule_ext fun n => by
    rw [restrictedGaloisRepresentation_seq, tateModule.representation_seq, restricted_smul_def]

/-- `φ ∈ K.fixingSubgroup` acts on `T_ℓ(A(Ω))` as `φ ∈ Gal(Ω/k)`. -/
theorem fixingSubgroupGaloisRepresentation_apply (φ : K.fixingSubgroup) :
    fixingSubgroupGaloisRepresentation ℓ K A φ =
      galoisRepresentation ℓ k Ω A (φ : Ω ≃ₐ[k] Ω) :=
  MonoidHom.comp_apply _ _ φ

/-- The representations of `K.fixingSubgroup` and of `Gal(Ω/K)` correspond under
`IntermediateField.fixingSubgroupEquiv K`. -/
theorem fixingSubgroupGaloisRepresentation_apply_eq (φ : K.fixingSubgroup) :
    fixingSubgroupGaloisRepresentation ℓ K A φ =
      restrictedGaloisRepresentation ℓ K A (IntermediateField.fixingSubgroupEquiv K φ) := by
  rw [fixingSubgroupGaloisRepresentation_apply, restrictedGaloisRepresentation_apply,
    NumberFieldGalois.restrictScalarsHom_fixingSubgroupEquiv]

/-- The finite-level compatibility for the fixing subgroup. -/
theorem tateReduction_fixingSubgroupGaloisRepresentation (n : ℕ) (φ : K.fixingSubgroup)
    (x : tateModule (GeomPoints k Ω A) ℓ) :
    tateReduction ℓ n (fixingSubgroupGaloisRepresentation ℓ K A φ x) =
      (φ : Ω ≃ₐ[k] Ω) • tateReduction ℓ n x := by
  rw [fixingSubgroupGaloisRepresentation_apply, tateReduction_galoisRepresentation]

variable [Algebra.IsAlgebraic k Ω] [LocallyOfFiniteType A.hom]

omit [GrpObj A] [IsCommMonObj A] in
variable (K) in
/-- For `Ω/k` algebraic and `A` locally of finite type over `k`, the stabilizer in `Gal(Ω/K)` of
every point of `A(Ω)` is open. -/
theorem isOpen_setOf_restrictScalarsHom_smul_eq (P : GeomPoints k Ω A) :
    IsOpen {σ : Ω ≃ₐ[K] Ω | AlgEquiv.restrictScalarsHom k σ • P = P} :=
  (GeomPoints.isOpen_setOf_smul_eq P).preimage (continuous_restrictScalarsHom (k := k) K)

variable (ℓ K A) in
/-- **Continuity of the restricted representation.** For `Ω/k` algebraic and `A` locally of
finite type over `k`, the action map `Gal(Ω/K) × T_ℓ(A(Ω)) → T_ℓ(A(Ω))` of
`restrictedGaloisRepresentation` is continuous (Krull topology on `Ω ≃ₐ[K] Ω`). -/
theorem continuous_restrictedGaloisRepresentation :
    Continuous fun p : (Ω ≃ₐ[K] Ω) × tateModule (GeomPoints k Ω A) ℓ =>
      restrictedGaloisRepresentation ℓ K A p.1 p.2 := by
  have h := (continuous_galoisRepresentation (K := k) (L := Ω) (A := A) ℓ).comp
    (((continuous_restrictScalarsHom (k := k) K).comp continuous_fst).prodMk continuous_snd)
  have e : (fun p : (Ω ≃ₐ[K] Ω) × tateModule (GeomPoints k Ω A) ℓ =>
      restrictedGaloisRepresentation ℓ K A p.1 p.2) =
      (fun p : (Ω ≃ₐ[k] Ω) × tateModule (GeomPoints k Ω A) ℓ =>
        galoisRepresentation ℓ k Ω A p.1 p.2) ∘
      fun p : (Ω ≃ₐ[K] Ω) × tateModule (GeomPoints k Ω A) ℓ =>
        (AlgEquiv.restrictScalarsHom k p.1, p.2) := by
    funext p
    exact LinearMap.congr_fun (restrictedGaloisRepresentation_apply p.1) p.2
  rw [e]
  exact h

variable (ℓ K A) in
/-- **Continuity of the representation of the fixing subgroup.** The action map
`K.fixingSubgroup × T_ℓ(A(Ω)) → T_ℓ(A(Ω))` is continuous (subspace topology from the Krull
topology of `Gal(Ω/k)`). -/
theorem continuous_fixingSubgroupGaloisRepresentation :
    Continuous fun p : K.fixingSubgroup × tateModule (GeomPoints k Ω A) ℓ =>
      fixingSubgroupGaloisRepresentation ℓ K A p.1 p.2 := by
  have h := (continuous_galoisRepresentation (K := k) (L := Ω) (A := A) ℓ).comp
    (((continuous_subtype_val : Continuous ((↑) : K.fixingSubgroup → Ω ≃ₐ[k] Ω)).comp
      continuous_fst).prodMk continuous_snd)
  have e : (fun p : K.fixingSubgroup × tateModule (GeomPoints k Ω A) ℓ =>
      fixingSubgroupGaloisRepresentation ℓ K A p.1 p.2) =
      (fun p : (Ω ≃ₐ[k] Ω) × tateModule (GeomPoints k Ω A) ℓ =>
        galoisRepresentation ℓ k Ω A p.1 p.2) ∘
      fun p : K.fixingSubgroup × tateModule (GeomPoints k Ω A) ℓ =>
        ((p.1 : Ω ≃ₐ[k] Ω), p.2) := by
    funext p
    exact LinearMap.congr_fun (fixingSubgroupGaloisRepresentation_apply p.1) p.2
  rw [e]
  exact h

end General

section Rat

variable (ℓ : ℕ) [Fact ℓ.Prime] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
  (A : Over (Spec (.of ℚ))) [GrpObj A] [IsCommMonObj A] [LocallyOfFiniteType A.hom]

/-- **Number fields.** For a commutative group scheme `A` locally of finite type over `ℚ`, a
prime `ℓ` and a number field `K ⊆ ℚ̄`, the representation of
`Gal(ℚ̄/K) = AlgebraicClosure ℚ ≃ₐ[K] AlgebraicClosure ℚ` on `T_ℓ(A(ℚ̄))` obtained by restricting
`galoisRepresentation` is continuous. -/
theorem rat_continuous_restrictedGaloisRepresentation :
    Continuous fun p : (AlgebraicClosure ℚ ≃ₐ[K] AlgebraicClosure ℚ) ×
        tateModule (GeomPoints ℚ (AlgebraicClosure ℚ) A) ℓ =>
      restrictedGaloisRepresentation ℓ K A p.1 p.2 :=
  continuous_restrictedGaloisRepresentation ℓ K A

/-- **Number fields.** The restriction of `galoisRepresentation` to the open subgroup
`Gal(ℚ̄/K) = K.fixingSubgroup ⊆ Gal(ℚ̄/ℚ)` is continuous. -/
theorem rat_continuous_fixingSubgroupGaloisRepresentation :
    Continuous fun p : K.fixingSubgroup ×
        tateModule (GeomPoints ℚ (AlgebraicClosure ℚ) A) ℓ =>
      fixingSubgroupGaloisRepresentation ℓ K A p.1 p.2 :=
  continuous_fixingSubgroupGaloisRepresentation ℓ K A

end Rat

end GroupScheme

end ArithmeticOfJacobiPolynomials
