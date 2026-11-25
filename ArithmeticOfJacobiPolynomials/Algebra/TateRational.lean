/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.TateAction
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# The rational Tate module `V_ℓ M = ℚ_ℓ ⊗_{ℤ_ℓ} T_ℓ M` (generic foundation)

Let `M` be an abelian group and `ℓ` a prime. The rational `ℓ`-adic Tate module is the scalar
extension `V_ℓ M = ℚ_ℓ ⊗_{ℤ_ℓ} T_ℓ M` of the Tate module of
`ArithmeticOfJacobiPolynomials.Algebra.TateModule`. An action of a monoid `G` on `M` by additive
maps induces the
representation `tateModule.representation` on `T_ℓ M`
(`ArithmeticOfJacobiPolynomials.Algebra.TateAction`) and,
by base change, a `ℚ_ℓ`-linear representation on `V_ℓ M`.

## Main definitions and results

* `ArithmeticOfJacobiPolynomials.rationalTate ℓ M`: `ℚ_[ℓ] ⊗[ℤ_[ℓ]] tateModule M ℓ`, a `ℚ_ℓ`-vector
space;
* `ArithmeticOfJacobiPolynomials.rationalTate.ofTate`: the `ℤ_ℓ`-linear map `T_ℓ M → V_ℓ M`, `x ↦ 1
⊗ x`;
* `ArithmeticOfJacobiPolynomials.rationalTate.representation ℓ M G : Representation ℚ_[ℓ] G
(rationalTate ℓ M)`:
  `g ↦ (ρ g).baseChange ℚ_ℓ`, with `rationalTate.representation_tmul` and the equivariance
  `rationalTate.representation_ofTate`;
* `ArithmeticOfJacobiPolynomials.finrank_rationalTate`: if `M` is `ℓ`-divisible and `M[ℓ^n] ≅
(ℤ/ℓ^n)^r` for every
  `n` (explicit hypotheses), then `dim_{ℚ_ℓ} V_ℓ M = r`.

This is generic: no specific group, Jacobian or Galois group is treated.
-/

public section

open PadicInt TensorProduct

namespace ArithmeticOfJacobiPolynomials

open Stacks.AbelianGroup

variable (ℓ : ℕ) [Fact ℓ.Prime] (M : Type*) [AddCommGroup M]

/-- The rational `ℓ`-adic Tate module `V_ℓ M = ℚ_ℓ ⊗_{ℤ_ℓ} T_ℓ M` of an abelian group `M`. -/
abbrev rationalTate : Type _ :=
  ℚ_[ℓ] ⊗[ℤ_[ℓ]] tateModule M ℓ

/-- The natural `ℤ_ℓ`-linear map `T_ℓ M → V_ℓ M`, `x ↦ 1 ⊗ x`. -/
@[expose]
noncomputable def rationalTate.ofTate : tateModule M ℓ →ₗ[ℤ_[ℓ]] rationalTate ℓ M :=
  TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (tateModule M ℓ) 1

variable {ℓ M} in
/-- `rationalTate.ofTate ℓ M x = 1 ⊗ x`. -/
theorem rationalTate.ofTate_apply (x : tateModule M ℓ) :
    rationalTate.ofTate ℓ M x = (1 : ℚ_[ℓ]) ⊗ₜ x :=
  rfl

section Representation

variable (G : Type*) [Monoid G] [DistribMulAction G M]

/-- The `ℚ_ℓ`-linear representation of `G` on `V_ℓ M = ℚ_ℓ ⊗_{ℤ_ℓ} T_ℓ M` obtained by scalar
extension of `tateModule.representation`: `g ↦ (ρ g).baseChange ℚ_ℓ`. -/
@[expose]
noncomputable def rationalTate.representation : Representation ℚ_[ℓ] G (rationalTate ℓ M) where
  toFun g := (tateModule.representation ℓ M G g).baseChange ℚ_[ℓ]
  map_one' := by
    simp only [_root_.map_one, Module.End.one_eq_id, LinearMap.baseChange_id]
  map_mul' g h := by
    simp only [_root_.map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp]

variable {ℓ M G}

/-- The representation on `V_ℓ M` is the base change of the representation on `T_ℓ M`. -/
theorem rationalTate.representation_apply (g : G) :
    rationalTate.representation ℓ M G g = (tateModule.representation ℓ M G g).baseChange ℚ_[ℓ] :=
  rfl

/-- `ρ_ℚ(g) (a ⊗ x) = a ⊗ ρ(g) x`. -/
@[simp]
theorem rationalTate.representation_tmul (g : G) (a : ℚ_[ℓ]) (x : tateModule M ℓ) :
    rationalTate.representation ℓ M G g (a ⊗ₜ x) = a ⊗ₜ tateModule.representation ℓ M G g x := by
  rw [rationalTate.representation_apply, LinearMap.baseChange_tmul]

/-- The map `T_ℓ M → V_ℓ M` is `G`-equivariant. -/
theorem rationalTate.representation_ofTate (g : G) (x : tateModule M ℓ) :
    rationalTate.representation ℓ M G g (rationalTate.ofTate ℓ M x) =
      rationalTate.ofTate ℓ M (tateModule.representation ℓ M G g x) := by
  rw [rationalTate.ofTate_apply, rationalTate.ofTate_apply, rationalTate.representation_tmul]

end Representation

section Rank

variable {ℓ M} {r : ℕ}

/-- If `M` is `ℓ`-divisible with `M[ℓ^n] ≅ (ℤ/ℓ^n)^r` for every `n` (explicit hypotheses), then
`V_ℓ M` is a finite-dimensional `ℚ_ℓ`-vector space. -/
theorem module_finite_rationalTate (hdiv : ∀ x : M, ∃ y, ℓ • y = x)
    (htors : ∀ n, Nonempty (AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ (Fin r → ZMod (ℓ ^ n)))) :
    Module.Finite ℚ_[ℓ] (rationalTate ℓ M) :=
  haveI := module_finite_tateModule hdiv htors
  inferInstance

/-- **Rank of the rational Tate module.** If `M` is `ℓ`-divisible with `M[ℓ^n] ≅ (ℤ/ℓ^n)^r` for
every `n` (explicit hypotheses), then `dim_{ℚ_ℓ} (ℚ_ℓ ⊗_{ℤ_ℓ} T_ℓ M) = r`. -/
theorem finrank_rationalTate (hdiv : ∀ x : M, ∃ y, ℓ • y = x)
    (htors : ∀ n, Nonempty (AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ (Fin r → ZMod (ℓ ^ n)))) :
    Module.finrank ℚ_[ℓ] (rationalTate ℓ M) = r := by
  have := module_free_tateModule hdiv htors
  have := module_finite_tateModule hdiv htors
  rw [Module.finrank_baseChange, finrank_tateModule hdiv htors]

end Rank

end ArithmeticOfJacobiPolynomials
