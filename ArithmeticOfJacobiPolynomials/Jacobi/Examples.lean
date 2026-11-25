/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.Reduction
public import ArithmeticOfJacobiPolynomials.Jacobi.CentralValue
public import ArithmeticOfJacobiPolynomials.Padic.IntegralLocalBound

/-!
# Worked examples stated in the manuscript

* §1.2, after Theorem 1.3: the restriction to large degree is necessary, since
  `P_2^{(4,1)}(x) = 3x(3x+2)` (`jacobiP_four_one_two`), which is reducible
  (`not_irreducible_jacobiP_four_one_two`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-- `P_2^{(4,1)}(x) = 3x(3x+2)`. -/
theorem jacobiP_four_one_two : jacobiP 4 1 2 = C 3 * X * (C 3 * X + C 2) := by
  have h := jacobiP_eq_C_mul_map_jacobiNum 4 1 2
  push_cast at h
  rw [h, jacobiNum_eq]
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.reduceAdd, Nat.reduceSub,
    Nat.choose_zero_right, Nat.choose_one_right, pow_zero, pow_one, mul_one,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_one, eq_intCast]
  norm_num [Nat.choose]
  apply Polynomial.funext
  intro x
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow, eval_ofNat, eval_one]
  ring

/-- `P_2^{(4,1)}` is reducible over `ℚ` (so Theorem 1.3 needs `n ≥ N(a,b)` with `N(4,1) ≥ 3`). -/
theorem not_irreducible_jacobiP_four_one_two : ¬ Irreducible (jacobiP 4 1 2) := by
  rw [jacobiP_four_one_two]
  intro h
  rcases h.isUnit_or_isUnit (a := C (3 : ℚ) * X) (b := C (3 : ℚ) * X + C 2) rfl with hu | hu
  · have h0 := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_C_mul_X _ (by norm_num)] at h0
    exact one_ne_zero h0
  · have h0 := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_linear (by norm_num)] at h0
    exact one_ne_zero h0

end ArithmeticOfJacobiPolynomials
