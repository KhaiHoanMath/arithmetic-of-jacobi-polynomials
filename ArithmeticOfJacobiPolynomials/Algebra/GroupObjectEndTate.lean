/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.GroupObjectEnd
public import ArithmeticOfJacobiPolynomials.Algebra.TateGeometricAction
public import ArithmeticOfJacobiPolynomials.Algebra.TateRational

/-!
# Action of the endomorphism ring of a commutative group scheme on its Tate modules

Let `A` be a commutative group scheme over a field `K` (`A : Over (Spec K)` with
`[GrpObj A] [IsCommMonObj A]`), `L/K` a field extension and `ℓ` a prime. The endomorphism ring
`GrpObjEnd A` acts on `A(L) = GeomPoints K L A` by the ring homomorphism `geomPointsAction`
(`ArithmeticOfJacobiPolynomials.Algebra.GroupObjectEnd`). Applying the functor `T_ℓ`:

* `ArithmeticOfJacobiPolynomials.tateModule.endRingHom ℓ M : AddMonoid.End M →+* Module.End ℤ_[ℓ]
(T_ℓ M)` is
  `f ↦ T_ℓ f` (generic, for any abelian group `M`);
* `ArithmeticOfJacobiPolynomials.rationalTate.endRingHom ℓ M` is the base change
  `Module.End ℤ_[ℓ] (T_ℓ M) →+* Module.End ℚ_[ℓ] (V_ℓ M)`;
* `ArithmeticOfJacobiPolynomials.GroupScheme.tateEndAction ℓ K L A : GrpObjEnd A →+* Module.End
ℤ_[ℓ] (T_ℓ(A(L)))`
  commutes with the Galois representation (`tateEndAction_galoisRepresentation`);
* `ArithmeticOfJacobiPolynomials.GroupScheme.rationalTateEndAction ℓ K L A`, the action on
  `V_ℓ(A(L)) = ℚ_ℓ ⊗ T_ℓ(A(L))`, commutes with `rationalTate.representation`
  (`rationalTateEndAction_comp_representation`).

This is generic: no statement about any specific `A` (no Jacobian, no computation of its
endomorphism ring) is made here.
-/

public section

open CategoryTheory AlgebraicGeometry PadicInt TensorProduct

universe u

namespace ArithmeticOfJacobiPolynomials

open Stacks.AbelianGroup

section Generic

variable (ℓ : ℕ) [Fact ℓ.Prime] (M : Type*) [AddCommGroup M]

/-- The functor `T_ℓ` on endomorphisms, `f ↦ T_ℓ f`, as a ring homomorphism
`End(M) →+* End_{ℤ_ℓ}(T_ℓ M)`. -/
@[expose]
noncomputable def tateModule.endRingHom :
    AddMonoid.End M →+* Module.End ℤ_[ℓ] (tateModule M ℓ) where
  toFun f := tateModuleMap ℓ f
  map_one' := tateModuleMap_id ℓ
  map_mul' f g := tateModuleMap_comp ℓ f g
  map_zero' := tateModuleMap_zero ℓ
  map_add' f g := tateModuleMap_add ℓ f g

variable {ℓ M} in
/-- `tateModule.endRingHom ℓ M f = T_ℓ f`. -/
theorem tateModule.endRingHom_apply (f : AddMonoid.End M) :
    tateModule.endRingHom ℓ M f = tateModuleMap ℓ f :=
  rfl

/-- Base change `φ ↦ ℚ_ℓ ⊗ φ` of endomorphisms of `T_ℓ M`, as a ring homomorphism
`End_{ℤ_ℓ}(T_ℓ M) →+* End_{ℚ_ℓ}(V_ℓ M)`. -/
@[expose]
noncomputable def rationalTate.endRingHom :
    Module.End ℤ_[ℓ] (tateModule M ℓ) →+* Module.End ℚ_[ℓ] (rationalTate ℓ M) where
  toFun φ := φ.baseChange ℚ_[ℓ]
  map_one' := LinearMap.baseChange_id
  map_mul' φ ψ := LinearMap.baseChange_comp (f := ψ) (g := φ)
  map_zero' := LinearMap.baseChange_zero
  map_add' φ ψ := LinearMap.baseChange_add (f := φ) (g := ψ)

variable {ℓ M} in
/-- `rationalTate.endRingHom ℓ M φ = φ.baseChange ℚ_ℓ`. -/
theorem rationalTate.endRingHom_apply (φ : Module.End ℤ_[ℓ] (tateModule M ℓ)) :
    rationalTate.endRingHom ℓ M φ = φ.baseChange ℚ_[ℓ] :=
  rfl

end Generic

namespace GroupScheme

open GroupObject

variable (ℓ : ℕ) [Fact ℓ.Prime] (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]
  (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]

/-- **Action of `End(A)` on the Tate module `T_ℓ(A(L))`:** `f ↦ T_ℓ(P ↦ P ≫ f)`, a ring
homomorphism `End(A) →+* End_{ℤ_ℓ}(T_ℓ(A(L)))`. -/
@[expose]
noncomputable def tateEndAction :
    GrpObjEnd A →+* Module.End ℤ_[ℓ] (tateModule (GeomPoints K L A) ℓ) :=
  (tateModule.endRingHom ℓ (GeomPoints K L A)).comp (geomPointsAction K L A)

/-- **Action of `End(A)` on the rational Tate module `V_ℓ(A(L)) = ℚ_ℓ ⊗ T_ℓ(A(L))`**, the base
change of `tateEndAction`. -/
@[expose]
noncomputable def rationalTateEndAction :
    GrpObjEnd A →+* Module.End ℚ_[ℓ] (rationalTate ℓ (GeomPoints K L A)) :=
  (rationalTate.endRingHom ℓ (GeomPoints K L A)).comp (tateEndAction ℓ K L A)

variable {ℓ K L A}

/-- `tateEndAction ℓ K L A f = T_ℓ (geomPointsAction K L A f)`. -/
theorem tateEndAction_apply (f : GrpObjEnd A) :
    tateEndAction ℓ K L A f = tateModuleMap ℓ (geomPointsAction K L A f) :=
  rfl

/-- The `n`-th component of `f • x` is `f (x n) = x n ≫ f`. -/
@[simp]
theorem tateEndAction_seq (f : GrpObjEnd A) (x : tateModule (GeomPoints K L A) ℓ) (n : ℕ) :
    ((tateEndAction ℓ K L A f x : tateModule (GeomPoints K L A) ℓ) : ℕ → GeomPoints K L A) n =
      geomPointsAction K L A f ((x : ℕ → GeomPoints K L A) n) :=
  rfl

/-- `rationalTateEndAction ℓ K L A f` is the base change of `tateEndAction ℓ K L A f`. -/
theorem rationalTateEndAction_apply (f : GrpObjEnd A) :
    rationalTateEndAction ℓ K L A f = (tateEndAction ℓ K L A f).baseChange ℚ_[ℓ] :=
  rfl

/-- `rationalTateEndAction ℓ K L A f (a ⊗ x) = a ⊗ tateEndAction ℓ K L A f x`. -/
theorem rationalTateEndAction_tmul (f : GrpObjEnd A) (a : ℚ_[ℓ])
    (x : tateModule (GeomPoints K L A) ℓ) :
    rationalTateEndAction ℓ K L A f (a ⊗ₜ x) = a ⊗ₜ tateEndAction ℓ K L A f x := by
  rw [rationalTateEndAction_apply, LinearMap.baseChange_tmul]

/-- **The action of `End(A)` on `T_ℓ(A(L))` commutes with the Galois representation:**
`f (σ x) = σ (f x)`. -/
theorem tateEndAction_galoisRepresentation (f : GrpObjEnd A) (σ : L ≃ₐ[K] L)
    (x : tateModule (GeomPoints K L A) ℓ) :
    tateEndAction ℓ K L A f (galoisRepresentation ℓ K L A σ x) =
      galoisRepresentation ℓ K L A σ (tateEndAction ℓ K L A f x) :=
  tateModule_ext fun n => by
    rw [tateEndAction_seq, galoisRepresentation_seq, galoisRepresentation_seq,
      tateEndAction_seq, geomPointsAction_smul]

/-- The action of `End(A)` on `T_ℓ(A(L))` commutes with the Galois representation, as an
equality of `ℤ_ℓ`-linear maps. -/
theorem tateEndAction_comp_galoisRepresentation (f : GrpObjEnd A) (σ : L ≃ₐ[K] L) :
    tateEndAction ℓ K L A f ∘ₗ galoisRepresentation ℓ K L A σ =
      galoisRepresentation ℓ K L A σ ∘ₗ tateEndAction ℓ K L A f :=
  LinearMap.ext fun x => tateEndAction_galoisRepresentation f σ x

/-- **The action of `End(A)` on `V_ℓ(A(L))` commutes with the Galois representation**
`rationalTate.representation` (the base change of `galoisRepresentation`). -/
theorem rationalTateEndAction_comp_representation (f : GrpObjEnd A) (σ : L ≃ₐ[K] L) :
    rationalTateEndAction ℓ K L A f ∘ₗ
        rationalTate.representation ℓ (GeomPoints K L A) (L ≃ₐ[K] L) σ =
      rationalTate.representation ℓ (GeomPoints K L A) (L ≃ₐ[K] L) σ ∘ₗ
        rationalTateEndAction ℓ K L A f := by
  rw [rationalTateEndAction_apply, rationalTate.representation_apply,
    ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
  exact congrArg (LinearMap.baseChange ℚ_[ℓ]) (tateEndAction_comp_galoisRepresentation f σ)

/-- Pointwise form of `rationalTateEndAction_comp_representation`. -/
theorem rationalTateEndAction_representation (f : GrpObjEnd A) (σ : L ≃ₐ[K] L)
    (v : rationalTate ℓ (GeomPoints K L A)) :
    rationalTateEndAction ℓ K L A f
        (rationalTate.representation ℓ (GeomPoints K L A) (L ≃ₐ[K] L) σ v) =
      rationalTate.representation ℓ (GeomPoints K L A) (L ≃ₐ[K] L) σ
        (rationalTateEndAction ℓ K L A f v) :=
  LinearMap.congr_fun (rationalTateEndAction_comp_representation f σ) v

end GroupScheme

end ArithmeticOfJacobiPolynomials
