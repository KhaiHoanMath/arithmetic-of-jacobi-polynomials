/- Assembled by AxiomProver. -/
module

public import StacksFrontier.Algebra.Group.TateModule

/-!
# Additional functoriality of the Stacks Tate module

The inverse limit, its scalar action, reduction, quotient, freeness and trace results
are imported from Stacks. This file only adds the induced linear equivalence for an
additive equivalence and an extensionality lemma stated using reductions.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Stacks.AbelianGroup

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] (ℓ : ℕ) [Fact ℓ.Prime]

/-- The `ℤ_[ℓ]`-linear isomorphism `T_ℓ M ≃ T_ℓ N` induced by an additive isomorphism
`e : M ≃+ N`. -/
@[expose]
noncomputable def tateModule.mapEquiv (e : M ≃+ N) : tateModule M ℓ ≃ₗ[ℤ_[ℓ]] tateModule N ℓ :=
  LinearEquiv.ofLinearMap (tateModuleMap ℓ e.toAddMonoidHom)
    (tateModuleMap ℓ e.symm.toAddMonoidHom)
    (by ext x n; simp) (by ext x n; simp)

variable {ℓ}

/-- `tateModule.mapEquiv ℓ e` acts as `tateModuleMap ℓ e`. -/
theorem tateModule.mapEquiv_apply (e : M ≃+ N) (x : tateModule M ℓ) :
    tateModule.mapEquiv ℓ e x = tateModuleMap ℓ e.toAddMonoidHom x :=
  rfl

/-- The `n`-th component of `T_ℓ e x` is `e (x n)`. -/
@[simp]
theorem tateModule.mapEquiv_seq (e : M ≃+ N) (x : tateModule M ℓ) (n : ℕ) :
    ((tateModule.mapEquiv ℓ e x : tateModule N ℓ) : ℕ → N) n = e ((x : ℕ → M) n) :=
  rfl

/-- The inverse of `T_ℓ e` is `T_ℓ e⁻¹`. -/
theorem tateModule.mapEquiv_symm_apply (e : M ≃+ N) (x : tateModule N ℓ) :
    (tateModule.mapEquiv ℓ e).symm x = tateModule.mapEquiv ℓ e.symm x :=
  rfl

omit [Fact ℓ.Prime] in
/-- An element of `T_ℓ M` is determined by its reductions. -/
theorem tateModule.ext_tateReduction {x y : tateModule M ℓ}
    (h : ∀ n, tateReduction ℓ n x = tateReduction ℓ n y) : x = y :=
  tateModule_ext fun n => congrArg Subtype.val (h n)

end ArithmeticOfJacobiPolynomials
