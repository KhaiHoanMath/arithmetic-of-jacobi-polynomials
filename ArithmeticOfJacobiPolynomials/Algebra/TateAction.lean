/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.TateModule
public import Mathlib.RepresentationTheory.Basic

/-!
# Group actions on the `ℓ`-adic Tate module of an abelian group (generic foundation)

Let a monoid `G` act on an abelian group `M` by additive endomorphisms (`DistribMulAction G M`).
Applying the functor `T_ℓ` of `ArithmeticOfJacobiPolynomials.Algebra.TateModule` to the action maps
`m ↦ g • m` gives an action of `G` on the same inverse limit `T_ℓ M = lim_n M[ℓ^n]`, by
`(g • x) n = g • x n`:

* `ArithmeticOfJacobiPolynomials.tateModule.representation ℓ M G : Representation ℤ_[ℓ] G
(tateModule M ℓ)`, a
  monoid homomorphism `G →* (T_ℓ M →ₗ[ℤ_ℓ] T_ℓ M)`;
* `ArithmeticOfJacobiPolynomials.tateModule.autRepresentation ℓ M G : G →* (T_ℓ M ≃ₗ[ℤ_ℓ] T_ℓ M)`
when `G` is a
  group;
* `tateModule.representation_seq`, `tateReduction_representation`: the action is computed
  componentwise and is compatible with the evaluations `T_ℓ M → M[ℓ^n]`.

This is a generic construction for an arbitrary abelian group with an action; it is not the
Galois representation on the Tate module of any specific Jacobian.
-/

public section

open PadicInt

namespace ArithmeticOfJacobiPolynomials

open Stacks.AbelianGroup

variable (ℓ : ℕ) [Fact ℓ.Prime] (M : Type*) [AddCommGroup M] (G : Type*)

section Monoid

variable [Monoid G] [DistribMulAction G M]

/-- The representation of `G` on `T_ℓ M` induced by an action of `G` on `M` by additive
endomorphisms: `g ↦ T_ℓ (m ↦ g • m)`. -/
@[expose]
noncomputable def tateModule.representation : Representation ℤ_[ℓ] G (tateModule M ℓ) where
  toFun g := tateModuleMap ℓ (DistribSMul.toAddMonoidHom M g)
  map_one' := by
    ext x n
    simp
  map_mul' g h := by
    ext x n
    simp [mul_smul]

variable {ℓ M G}

/-- The action of `g` on `T_ℓ M` is `T_ℓ` of the action of `g` on `M`. -/
theorem tateModule.representation_apply (g : G) :
    tateModule.representation ℓ M G g = tateModuleMap ℓ (DistribSMul.toAddMonoidHom M g) :=
  rfl

/-- The `n`-th component of `g • x` is `g • x n`. -/
@[simp]
theorem tateModule.representation_seq (g : G) (x : tateModule M ℓ) (n : ℕ) :
    ((tateModule.representation ℓ M G g x : tateModule M ℓ) : ℕ → M) n = g • (x : ℕ → M) n := by
  rw [tateModule.representation_apply, tateModuleMap_seq, DistribSMul.toAddMonoidHom_apply]

/-- The action of `G` on `T_ℓ M` is compatible with the evaluation `T_ℓ M → M[ℓ^n]`. -/
theorem tateReduction_representation (n : ℕ) (g : G) (x : tateModule M ℓ) :
    (tateReduction ℓ n (tateModule.representation ℓ M G g x) : M) =
      g • (tateReduction ℓ n x : M) :=
  tateModule.representation_seq g x n

end Monoid

section Group

variable [Group G] [DistribMulAction G M]

/-- For a group `G` acting on `M` by additive automorphisms, the induced action on `T_ℓ M` by
`ℤ_ℓ`-linear automorphisms: `g ↦ T_ℓ (m ↦ g • m)`. -/
@[expose]
noncomputable def tateModule.autRepresentation :
    G →* (tateModule M ℓ ≃ₗ[ℤ_[ℓ]] tateModule M ℓ) where
  toFun g := tateModule.mapEquiv ℓ (DistribMulAction.toAddEquiv M g)
  map_one' := by
    ext x n
    simp
  map_mul' g h := by
    ext x n
    simp [LinearEquiv.mul_apply, mul_smul]

variable {ℓ M G}

/-- The `n`-th component of the automorphism attached to `g`, applied to `x`, is `g • x n`. -/
@[simp]
theorem tateModule.autRepresentation_seq (g : G) (x : tateModule M ℓ) (n : ℕ) :
    ((tateModule.autRepresentation ℓ M G g x : tateModule M ℓ) : ℕ → M) n =
      g • (x : ℕ → M) n := by
  change ((tateModule.mapEquiv ℓ (DistribMulAction.toAddEquiv M g) x : tateModule M ℓ) : ℕ → M) n
    = _
  rw [tateModule.mapEquiv_seq, DistribMulAction.toAddEquiv_apply]

/-- The automorphisms `tateModule.autRepresentation` are the linear maps of
`tateModule.representation`. -/
theorem tateModule.coe_autRepresentation (g : G) :
    (tateModule.autRepresentation ℓ M G g : tateModule M ℓ →ₗ[ℤ_[ℓ]] tateModule M ℓ) =
      tateModule.representation ℓ M G g := by
  ext x n
  simp

end Group

end ArithmeticOfJacobiPolynomials
