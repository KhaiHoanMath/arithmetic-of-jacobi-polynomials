/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.DifferentialEquation
public import ArithmeticOfJacobiPolynomials.Jacobi.SymmetricCoefficients
public import ArithmeticOfJacobiPolynomials.Jacobi.IntegralWeights

/-!
# Derivatives of Legendre polynomials as Jacobi polynomials

For integers `r ≥ 0` and `n ≥ 0`, `f = P_{n+r}^{(r)} = (2r-1)!! C_n^{r+1/2}` is a nonzero
rational multiple of `P_n^{(r,r)}`. The Gegenbauer form of this relation, for every rational
`a > -1` in place of the integer `r`, is `gegenbauerC_eq_C_mul_jacobiP` in
`ArithmeticOfJacobiPolynomials.Jacobi.SymmetricGegenbauer` ([DLMF, 18.7.1]); here we prove
the normalized identities for `f` needed in the local argument of Lemma 2.4 and Theorem 3.4,
by the uniqueness of polynomial solutions of the shifted Jacobi equation
`t(t+1) z'' + [(α+1) + (α+β+2) t] z' = n(n+α+β+1) z` (for `α > -1` a solution is determined
by its constant coefficient, through the two-term recurrence of its coefficients).

Main results:
* `ArithmeticOfJacobiPolynomials.iterate_derivative_legendreP_comp_eq`: `f(2X+1) = f(1) Q`, where
  `Q = P_n^{(r,r)}(2X+1) / binom(n+r, r)` is the polynomial of Lemma 2.4
  (`integralWeightQ r r n`);
* `ArithmeticOfJacobiPolynomials.iterate_derivative_legendreP_eq_jacobiP`:
  `f = (f(1) / binom(n+r, r)) P_n^{(r,r)}`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-- The coefficient recurrence of a solution of the shifted Jacobi equation:
`(j+1)(j+α+1) y_{j+1} = (n-j)(n+j+α+β+1) y_j`. -/
theorem shift_ode_coeff_recurrence {α β : ℚ} {n : ℕ} {y : ℚ[X]}
    (hy : X * (X + 1) * derivative (derivative y) +
      (C (α + 1) + C (α + β + 2) * X) * derivative y = C ((n : ℚ) * (n + α + β + 1)) * y)
    (j : ℕ) :
    ((j : ℚ) + 1) * (j + α + 1) * y.coeff (j + 1) =
      ((n : ℚ) - j) * (n + j + α + β + 1) * y.coeff j := by
  have key : X * (X + 1) * derivative (derivative y) +
      (C (α + 1) + C (α + β + 2) * X) * derivative y =
      X * derivative (X * derivative y) - X * derivative y + X * derivative (derivative y) +
        C (α + 1) * derivative y + C (α + β + 2) * (X * derivative y) := by
    rw [derivative_mul, derivative_X]; ring
  have h := congrArg (fun q => q.coeff j) (key.symm.trans hy)
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul_derivative, coeff_derivative] at h
  linear_combination h

/-- Uniqueness for the shifted Jacobi equation: for `α > -1`, two polynomial solutions `y, z`
satisfy `z(0) y = y(0) z`. -/
theorem C_mul_eq_C_mul_of_shift_ode {α β : ℚ} (hα : -1 < α) {n : ℕ} {y z : ℚ[X]}
    (hy : X * (X + 1) * derivative (derivative y) +
      (C (α + 1) + C (α + β + 2) * X) * derivative y = C ((n : ℚ) * (n + α + β + 1)) * y)
    (hz : X * (X + 1) * derivative (derivative z) +
      (C (α + 1) + C (α + β + 2) * X) * derivative z = C ((n : ℚ) * (n + α + β + 1)) * z) :
    C (z.coeff 0) * y = C (y.coeff 0) * z := by
  ext j
  simp only [coeff_C_mul]
  induction j with
  | zero => ring
  | succ j ih =>
    have h1 := shift_ode_coeff_recurrence hy j
    have h2 := shift_ode_coeff_recurrence hz j
    have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    have hne : ((j : ℚ) + 1) * (j + α + 1) ≠ 0 :=
      (mul_pos (by linarith) (by linarith)).ne'
    apply mul_left_cancel₀ hne
    linear_combination (z.coeff 0) * h1 - (y.coeff 0) * h2 +
      ((n : ℚ) - j) * (n + j + α + β + 1) * ih

/-- `f = P_{n+r}^{(r)}` satisfies the shifted Jacobi equation with `α = β = r`:
`t(t+1) g'' + (r+1)(1+2t) g' = n(n+2r+1) g` for `g = f(2t+1)`. -/
theorem iterate_derivative_legendreP_comp_shift_ode (n r : ℕ) :
    X * (X + 1) * derivative (derivative ((derivative^[r] (legendreP (n + r))).comp
        (2 * X + 1))) +
      (C ((r : ℚ) + 1) + C ((r : ℚ) + r + 2) * X) *
        derivative ((derivative^[r] (legendreP (n + r))).comp (2 * X + 1)) =
      C ((n : ℚ) * (n + r + r + 1)) * (derivative^[r] (legendreP (n + r))).comp (2 * X + 1) := by
  set f := derivative^[r] (legendreP (n + r)) with hf
  have hz1 : derivative (f.comp (2 * X + 1)) = 2 * (derivative f).comp (2 * X + 1) := by
    rw [derivative_comp]; simp
  have hz2 : derivative (derivative (f.comp (2 * X + 1))) =
      4 * (derivative (derivative f)).comp (2 * X + 1) := by
    rw [hz1, derivative_mul, derivative_comp]; simp; ring
  have hode := congrArg (fun q => q.comp (2 * X + 1))
    (iterate_derivative_legendreP_differential_equation n r)
  simp only [add_comp, mul_comp, sub_comp, one_comp, pow_comp, X_comp, C_comp, zero_comp]
    at hode
  rw [← hf] at hode
  rw [hz2, hz1]
  simp only [map_add, map_mul, map_natCast, map_one, map_ofNat] at hode ⊢
  linear_combination -hode

/-- The constant coefficient of `P_n^{(r,r)}(2X+1)` is `binom(n+r, r)`. -/
theorem coeff_zero_jacobiP_comp_two_mul_X_add_one (n r : ℕ) :
    ((jacobiP r r n).comp (2 * X + 1)).coeff 0 = ((n + r).choose r : ℚ) := by
  rw [coeff_jacobiP_comp_two_mul_X_add_one]
  simp only [zero_le, ↓reduceIte, Nat.sub_zero, Nat.cast_zero, add_zero, Ring.choose_zero_right,
    mul_one]
  rw [show ((n : ℚ) + r) = ((n + r : ℕ) : ℚ) by push_cast; ring, Ring.choose_natCast,
    Nat.choose_symm_add]

/-- **The Jacobi form of `P_{n+r}^{(r)}`, shifted.** With `f = P_{n+r}^{(r)}`,
`f(2X+1) = f(1) Q`, where `Q = P_n^{(r,r)}(2X+1) / binom(n+r, r)` (`integralWeightQ r r n`). -/
theorem iterate_derivative_legendreP_comp_eq (n r : ℕ) :
    (derivative^[r] (legendreP (n + r))).comp (2 * X + 1) =
      C ((derivative^[r] (legendreP (n + r))).eval 1) * integralWeightQ r r n := by
  have hα : (-1 : ℚ) < r := by have := (Nat.cast_nonneg r : (0 : ℚ) ≤ r); linarith
  set f := derivative^[r] (legendreP (n + r)) with hf
  have huniq := C_mul_eq_C_mul_of_shift_ode hα (iterate_derivative_legendreP_comp_shift_ode n r)
    (jacobiP_shift_ode (r : ℚ) (r : ℚ) n)
  have h0 : (f.comp (2 * X + 1)).coeff 0 = f.eval 1 := by
    rw [coeff_zero_eq_eval_zero, eval_comp]; simp
  rw [coeff_zero_jacobiP_comp_two_mul_X_add_one, h0] at huniq
  have hB : ((n + r).choose r : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  rw [integralWeightQ_eq]
  calc f.comp (2 * X + 1) = C (1 / ((n + r).choose r : ℚ)) *
        (C ((n + r).choose r : ℚ) * f.comp (2 * X + 1)) := by
        rw [← mul_assoc, ← C_mul, one_div_mul_cancel hB, C_1, one_mul]
    _ = C (1 / ((n + r).choose r : ℚ)) * (C (f.eval 1) * (jacobiP r r n).comp (2 * X + 1)) := by
        rw [huniq]
    _ = _ := by ring

/-- **The Jacobi form of `P_{n+r}^{(r)}`.** `f = (f(1) / binom(n+r, r)) P_n^{(r,r)}`. -/
theorem iterate_derivative_legendreP_eq_jacobiP (n r : ℕ) :
    derivative^[r] (legendreP (n + r)) =
      C ((derivative^[r] (legendreP (n + r))).eval 1 / ((n + r).choose r : ℚ)) *
        jacobiP r r n := by
  have hinv : (2 * X + 1 : ℚ[X]).comp (C (1 / 2) * (X - 1)) = X := by
    rw [show (2 * X + 1 : ℚ[X]) = C 2 * X + C 1 by simp [C_ofNat]]
    simp only [add_comp, mul_comp, X_comp, C_comp]
    rw [← mul_assoc, ← C_mul]
    norm_num
  have h := congrArg (fun q => q.comp (C (1 / 2) * (X - 1)))
    (iterate_derivative_legendreP_comp_eq n r)
  simp only [comp_assoc, hinv, comp_X, mul_comp, C_comp, integralWeightQ_eq] at h
  conv_lhs => rw [h]
  rw [← mul_assoc, ← C_mul]
  congr 2
  ring

/-- `P_{n+r}^{(r)}(1) ≠ 0`. -/
theorem iterate_derivative_legendreP_eval_one_ne_zero (n r : ℕ) :
    (derivative^[r] (legendreP (n + r))).eval 1 ≠ 0 :=
  (eval_one_iterate_derivative_legendreP_pos n r).ne'

end ArithmeticOfJacobiPolynomials
