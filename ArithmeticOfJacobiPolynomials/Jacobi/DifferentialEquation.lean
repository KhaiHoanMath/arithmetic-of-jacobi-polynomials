/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.Shift
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Tactic.LinearCombination

/-!
# The Jacobi differential equation

Eq. (5.6) of the manuscript (§5.1, [DLMF, Table 18.8.1]):
`(1 - X^2) y'' + [β - α - (α + β + 2) X] y' + n (n + α + β + 1) y = 0` for
`y = P_n^{(α,β)}`, as a polynomial identity. We prove it from the endpoint expansion (5.4)
by coefficient comparison: in the variable `t` with `x = 2t + 1` it reads
`t(t+1) z'' + [(α + 1) + (α + β + 2) t] z' = n (n + α + β + 1) z`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-- `binom(r, k+1) (k+1) = binom(r, k) (r - k)`. -/
theorem ring_choose_succ_mul (r : ℚ) (k : ℕ) :
    Ring.choose r (k + 1) * ((k : ℚ) + 1) = Ring.choose r k * (r - k) := by
  have h := Ring.choose_smul_choose r (n := k + 1) (k := k) (by omega)
  rw [Nat.choose_succ_self_right, nsmul_eq_mul, show k + 1 - k = 1 by omega,
    Ring.choose_one_right] at h
  rw [mul_comm, ← h]; push_cast; ring

/-- `binom(r+1, k+1) (k+1) = (r+1) binom(r, k)`. -/
theorem ring_choose_add_one_succ_mul (r : ℚ) (k : ℕ) :
    Ring.choose (r + 1) (k + 1) * ((k : ℚ) + 1) = (r + 1) * Ring.choose r k := by
  have h := Ring.choose_smul_choose (r + 1) (n := k + 1) (k := 1) (by omega)
  rw [Nat.choose_one_right, nsmul_eq_mul, Ring.choose_one_right,
    show k + 1 - 1 = k by omega] at h
  simp only [Nat.cast_one, add_sub_cancel_right] at h
  rw [mul_comm, ← h]; push_cast; ring

/-- The Euler operator on coefficients: `[X^j] (X p') = j [X^j] p`. -/
theorem coeff_X_mul_derivative {R : Type*} [CommSemiring R] (p : R[X]) (j : ℕ) :
    (X * derivative p).coeff j = j * p.coeff j := by
  cases j with
  | zero => simp
  | succ i => rw [coeff_X_mul, coeff_derivative]; push_cast; ring

/-- The coefficients of `P_n^{(α,β)}(2X+1)`. -/
theorem coeff_jacobiP_comp_two_mul_X_add_one (α β : ℚ) (n j : ℕ) :
    ((jacobiP α β n).comp (2 * X + 1)).coeff j = if j ≤ n then
      Ring.choose ((n : ℚ) + α) (n - j) * Ring.choose ((n : ℚ) + α + β + j) j else 0 := by
  rw [jacobiP_comp_two_mul_X_add_one, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq, mem_range, Nat.lt_succ_iff]

/-- The two-term coefficient recurrence of `P_n^{(α,β)}(2X+1)`. -/
theorem jacobiP_shift_coeff_recurrence (α β : ℚ) (n j : ℕ) :
    ((j : ℚ) + 1) * (j + α + 1) * ((jacobiP α β n).comp (2 * X + 1)).coeff (j + 1) =
      ((n : ℚ) - j) * (n + j + α + β + 1) * ((jacobiP α β n).comp (2 * X + 1)).coeff j := by
  rw [coeff_jacobiP_comp_two_mul_X_add_one, coeff_jacobiP_comp_two_mul_X_add_one]
  rcases lt_trichotomy j n with hjn | hjn | hjn
  · have hj1 : j + 1 ≤ n := hjn
    simp only [hj1, hjn.le, ↓reduceIte]
    obtain ⟨m, hm⟩ : ∃ m, n - j = m + 1 := ⟨n - j - 1, by omega⟩
    have hm' : n - (j + 1) = m := by omega
    rw [hm, hm']
    have hmq : (m : ℚ) = n - j - 1 := by
      have : m + j + 1 = n := by omega
      rw [← this]; push_cast; ring
    have h1 := ring_choose_succ_mul ((n : ℚ) + α) m
    have h2 := ring_choose_add_one_succ_mul ((n : ℚ) + α + β + j) j
    have e : ((n : ℚ) + α + β + ((j + 1 : ℕ) : ℚ)) = (n : ℚ) + α + β + j + 1 := by
      push_cast; ring
    rw [e]
    rw [hmq] at h1
    have e2 : ((n : ℚ) - j) = (n - j - 1) + 1 := by ring
    rw [e2]
    linear_combination (↑j + α + 1) * Ring.choose (↑n + α) m * h2 -
      (↑n + ↑j + α + β + 1) * Ring.choose (↑n + α + β + ↑j) j * h1
  · subst hjn; simp
  · have hj1 : ¬ j + 1 ≤ n := by omega
    have hj2 : ¬ j ≤ n := by omega
    simp only [hj1, hj2, ↓reduceIte, mul_zero]

/-- The Jacobi differential equation in the variable `t`, `x = 2t + 1`:
`t(t+1) z'' + [(α+1) + (α+β+2) t] z' = n(n+α+β+1) z` for `z = P_n^{(α,β)}(2t+1)`. -/
theorem jacobiP_shift_ode (α β : ℚ) (n : ℕ) :
    X * (X + 1) * derivative (derivative ((jacobiP α β n).comp (2 * X + 1))) +
      (C (α + 1) + C (α + β + 2) * X) * derivative ((jacobiP α β n).comp (2 * X + 1)) =
      C ((n : ℚ) * (n + α + β + 1)) * (jacobiP α β n).comp (2 * X + 1) := by
  set z := (jacobiP α β n).comp (2 * X + 1) with hz
  have key : X * (X + 1) * derivative (derivative z) +
      (C (α + 1) + C (α + β + 2) * X) * derivative z =
      X * derivative (X * derivative z) - X * derivative z + X * derivative (derivative z) +
        C (α + 1) * derivative z + C (α + β + 2) * (X * derivative z) := by
    rw [derivative_mul, derivative_X]; ring
  rw [key]
  ext j
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul_derivative, coeff_derivative]
  have hr := jacobiP_shift_coeff_recurrence α β n j
  rw [← hz] at hr
  linear_combination hr

/-- **The Jacobi differential equation (5.6)**:
`(1 - X^2) y'' + [β - α - (α + β + 2) X] y' + n (n + α + β + 1) y = 0` for
`y = P_n^{(α,β)}`. -/
theorem jacobiP_ode (α β : ℚ) (n : ℕ) :
    (1 - X ^ 2) * derivative (derivative (jacobiP α β n)) +
      (C (β - α) - C (α + β + 2) * X) * derivative (jacobiP α β n) +
      C ((n : ℚ) * (n + α + β + 1)) * jacobiP α β n = 0 := by
  set y := jacobiP α β n with hy
  set E := (1 - X ^ 2) * derivative (derivative y) +
      (C (β - α) - C (α + β + 2) * X) * derivative y + C ((n : ℚ) * (n + α + β + 1)) * y
    with hE
  have hz1 : derivative (y.comp (2 * X + 1)) = 2 * (derivative y).comp (2 * X + 1) := by
    rw [derivative_comp]; simp
  have hz2 : derivative (derivative (y.comp (2 * X + 1))) =
      4 * (derivative (derivative y)).comp (2 * X + 1) := by
    rw [hz1, derivative_mul, derivative_comp]; simp; ring
  have hode := jacobiP_shift_ode α β n
  rw [← hy] at hode
  have hEc : E.comp (2 * X + 1) = 0 := by
    rw [hE]
    simp only [add_comp, mul_comp, sub_comp, one_comp, pow_comp, X_comp, C_comp]
    rw [hz2, hz1] at hode
    simp only [map_add, map_sub, map_one, map_ofNat] at hode ⊢
    linear_combination -hode
  have hinv : (2 * X + 1 : ℚ[X]).comp (C (1 / 2) * (X - 1)) = X := by
    rw [show (2 * X + 1 : ℚ[X]) = C 2 * X + C 1 by simp [C_ofNat]]
    simp only [add_comp, mul_comp, X_comp, C_comp]
    rw [← mul_assoc, ← C_mul]
    norm_num
  calc E = E.comp X := (comp_X).symm
    _ = (E.comp (2 * X + 1)).comp (C (1 / 2) * (X - 1)) := by rw [comp_assoc, hinv]
    _ = 0 := by rw [hEc, zero_comp]

end ArithmeticOfJacobiPolynomials
