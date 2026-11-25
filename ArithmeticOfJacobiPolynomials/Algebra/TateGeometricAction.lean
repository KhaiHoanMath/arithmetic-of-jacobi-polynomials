/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.TateAction
public import ArithmeticOfJacobiPolynomials.Geometry.GroupSchemeGeometricPoints

/-!
# The Galois representation on the Tate module of the geometric points of a group scheme

Let `K` be a field, `L/K` a field extension (e.g. `AlgebraicClosure K`), `A` a commutative group
scheme over `K` (`A : Over (Spec K)` with `[GrpObj A] [IsCommMonObj A]`) and `ℓ` a prime. The
group `A(L) = GeomPoints K L A` of `L`-points carries the action of `L ≃ₐ[K] L` by group
automorphisms (`ArithmeticOfJacobiPolynomials.Geometry.GroupSchemeGeometricPoints`). Applying the
generic action
API of `ArithmeticOfJacobiPolynomials.Algebra.TateAction` gives:

* `ArithmeticOfJacobiPolynomials.GroupScheme.galoisRepresentation ℓ K L A`: the representation
  `Representation ℤ_[ℓ] (L ≃ₐ[K] L) (tateModule (GeomPoints K L A) ℓ)` on `T_ℓ(A(L))`;
* `ArithmeticOfJacobiPolynomials.GroupScheme.galoisAutRepresentation ℓ K L A`: the same action as a
monoid
  homomorphism to `ℤ_ℓ`-linear automorphisms;
* `galoisRepresentation_seq`, `tateReduction_galoisRepresentation`: the action is computed
  componentwise on `A(L)[ℓ^n]`, compatibly with the Galois action on the torsion subgroups.

This is generic: no Jacobian, no rank of the Tate module, no continuity for the profinite
topology on the Galois group and no Weil pairing are treated here.
-/

public section

open CategoryTheory AlgebraicGeometry PadicInt

universe u

namespace ArithmeticOfJacobiPolynomials

open Stacks.AbelianGroup

namespace GroupScheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]
  (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]

/-- The representation of `L ≃ₐ[K] L` on the `ℓ`-adic Tate module `T_ℓ(A(L))` of the group of
`L`-points of `A`, induced by the action `σ • P = Spec σ ≫ P` on `A(L)`. -/
@[expose]
noncomputable def galoisRepresentation :
    Representation ℤ_[ℓ] (L ≃ₐ[K] L) (tateModule (GeomPoints K L A) ℓ) :=
  tateModule.representation ℓ (GeomPoints K L A) (L ≃ₐ[K] L)

/-- The action of `L ≃ₐ[K] L` on `T_ℓ(A(L))` by `ℤ_ℓ`-linear automorphisms. -/
@[expose]
noncomputable def galoisAutRepresentation :
    (L ≃ₐ[K] L) →* (tateModule (GeomPoints K L A) ℓ ≃ₗ[ℤ_[ℓ]] tateModule (GeomPoints K L A) ℓ) :=
  tateModule.autRepresentation ℓ (GeomPoints K L A) (L ≃ₐ[K] L)

variable {ℓ K L A}

/-- The `n`-th component of `σ • x` is `σ • x n = Spec σ ≫ x n`. -/
@[simp]
theorem galoisRepresentation_seq (σ : L ≃ₐ[K] L) (x : tateModule (GeomPoints K L A) ℓ)
    (n : ℕ) :
    ((galoisRepresentation ℓ K L A σ x : tateModule (GeomPoints K L A) ℓ) :
        ℕ → GeomPoints K L A) n = σ • (x : ℕ → GeomPoints K L A) n :=
  tateModule.representation_seq σ x n

/-- On underlying morphisms, the `n`-th component of `σ • x` is `Spec σ ≫ x n`. -/
theorem toHom_galoisRepresentation_seq (σ : L ≃ₐ[K] L)
    (x : tateModule (GeomPoints K L A) ℓ) (n : ℕ) :
    GeomPoints.toHom K L A
        (((galoisRepresentation ℓ K L A σ x : tateModule (GeomPoints K L A) ℓ) :
          ℕ → GeomPoints K L A) n) =
      specAut K L σ ≫ GeomPoints.toHom K L A ((x : ℕ → GeomPoints K L A) n) := by
  rw [galoisRepresentation_seq, GeomPoints.toHom_smul]

/-- The Galois action on `T_ℓ(A(L))` is compatible with the evaluations
`T_ℓ(A(L)) → A(L)[ℓ^n]` and the Galois action on `A(L)[ℓ^n]`. -/
theorem tateReduction_galoisRepresentation (n : ℕ) (σ : L ≃ₐ[K] L)
    (x : tateModule (GeomPoints K L A) ℓ) :
    tateReduction ℓ n (galoisRepresentation ℓ K L A σ x) = σ • tateReduction ℓ n x :=
  Subtype.ext (tateReduction_representation n σ x)

/-- The automorphism attached to `σ` acts on `T_ℓ(A(L))` as `galoisRepresentation`. -/
theorem galoisAutRepresentation_apply (σ : L ≃ₐ[K] L) (x : tateModule (GeomPoints K L A) ℓ) :
    galoisAutRepresentation ℓ K L A σ x = galoisRepresentation ℓ K L A σ x :=
  LinearMap.congr_fun (tateModule.coe_autRepresentation σ) x

end GroupScheme

end ArithmeticOfJacobiPolynomials
