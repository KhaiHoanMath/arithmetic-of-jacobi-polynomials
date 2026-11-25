/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Remarks.Chebyshev
public import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# The Chebyshev specialization over Mathlib's `CyclotomicField`

The unconditional form of the abelian-Galois-group assertion of the remark after Theorem 1.6,
obtained by instantiating `jacobiP_neg_half_neg_half_gal_mul_comm_of_isCyclotomicExtension` at
Mathlib's `CyclotomicField (4n) ℚ`:

* `jacobiP_neg_half_neg_half_gal_mul_comm`: the Galois group of `P_n^{(-1/2,-1/2)}` over `ℚ` is
  abelian.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-- **Remark after Theorem 1.6.** For `n ≥ 1`, the Galois group of `P_n^{(-1/2,-1/2)}` over `ℚ`
is abelian. -/
theorem jacobiP_neg_half_neg_half_gal_mul_comm (n : ℕ) (hn : 1 ≤ n)
    (σ τ : (jacobiP (-1 / 2) (-1 / 2) n).Gal) : σ * τ = τ * σ := by
  let _ := CyclotomicField.algebra (4 * n) ℚ
  have : NeZero (4 * n) := ⟨by omega⟩
  have : NeZero ((4 * n : ℕ) : ℚ) := ⟨by exact_mod_cast (show 4 * n ≠ 0 by omega)⟩
  have : IsCyclotomicExtension {4 * n} ℚ (CyclotomicField (4 * n) ℚ) :=
    CyclotomicField.isCyclotomicExtension (4 * n) ℚ
  exact jacobiP_neg_half_neg_half_gal_mul_comm_of_isCyclotomicExtension n hn
    (CyclotomicField (4 * n) ℚ) σ τ

end ArithmeticOfJacobiPolynomials
