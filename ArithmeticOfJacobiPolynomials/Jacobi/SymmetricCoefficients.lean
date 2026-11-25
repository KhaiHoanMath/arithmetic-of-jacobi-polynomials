/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.Gegenbauer
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases

/-!
# Coefficients and endpoint values of `f = P_{n+r}^{(r)}` (symmetric case)

For `f = dʳ/dxʳ P_{n+r}` (Section 3.2 of the manuscript, proof of Theorem 3.4) we
prove:

* the single coefficients of (3.10) and the vanishing of the coefficients of the wrong parity;
* (3.11), the central coefficient `[x^δ] f = (-1)^m (2m+2r+2δ-1)!! / (2^m m!)`, `n = 2m+δ`;
* the leading coefficient `lc(f) = (2n+2r-1)!!/n!` and `deg f = n`;
* the parity `f(-x) = (-1)^n f(x)`;
* the differential equation `(1-x²) f'' - (2r+2) x f' + n(n+2r+1) f = 0`;
* (3.14), `f(1) = (n+2r)! / (2^r r! n!) = binom(n+2r, 2r) (2r-1)!!` and `|f(-1)| = f(1)`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-- **Eq. (3.10), coefficientwise.** For `k ≤ n/2`, the coefficient of `x^{n-2k}` in
`f = P_{n+r}^{(r)}` is `2^{-n-r} (-1)^k (2n+2r-2k)! / (k! (n+r-k)! (n-2k)!)`. -/
theorem coeff_iterate_derivative_legendreP (n r k : ℕ) (hk : k ≤ n / 2) :
    (derivative^[r] (legendreP (n + r))).coeff (n - 2 * k) =
      (1 / 2 : ℚ) ^ (n + r) * ((-1) ^ k * ((2 * n + 2 * r - 2 * k).factorial : ℚ) /
        ((k.factorial : ℚ) * ((n + r - k).factorial : ℚ) * ((n - 2 * k).factorial : ℚ))) := by
  rw [iterate_derivative_legendreP, coeff_C_mul, finsetSum_coeff, sum_eq_single k]
  · simp only [coeff_C_mul_X_pow, ite_true]
  · intro j hj hjk
    have hj : j ≤ n / 2 := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rw [coeff_C_mul_X_pow, ite_eq_right_iff.mpr fun h => absurd h (by omega)]
  · intro h; exact absurd (mem_range.mpr (Nat.lt_succ_of_le hk)) h

/-- The coefficients of `f = P_{n+r}^{(r)}` vanish in degrees of the wrong parity. -/
theorem coeff_iterate_derivative_legendreP_eq_zero_of_odd (n r i : ℕ) (h : Odd (n + i)) :
    (derivative^[r] (legendreP (n + r))).coeff i = 0 := by
  rw [iterate_derivative_legendreP, coeff_C_mul, finsetSum_coeff]
  refine mul_eq_zero_of_right _ (sum_eq_zero fun j hj => ?_)
  have hj : j ≤ n / 2 := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [coeff_C_mul_X_pow, ite_eq_right_iff.mpr fun h' => absurd h' ?_]
  rintro rfl
  obtain ⟨t, ht⟩ := h
  omega

theorem natDegree_iterate_derivative_legendreP_le (n r : ℕ) :
    (derivative^[r] (legendreP (n + r))).natDegree ≤ n := by
  rw [iterate_derivative_legendreP]
  refine (natDegree_C_mul_le _ _).trans ?_
  exact natDegree_sum_le_of_forall_le _ _ fun k _ =>
    (natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le _ _)

/-- **Eq. (3.11).** For `n = 2m+δ`, `δ ∈ {0,1}`, the central coefficient of
`f = P_{n+r}^{(r)}` is `[x^δ] f = (-1)^m (2m+2r+2δ-1)!! / (2^m m!)`. -/
theorem coeff_iterate_derivative_legendreP_center (m r δ : ℕ) (hδ : δ ≤ 1) :
    (derivative^[r] (legendreP (2 * m + δ + r))).coeff δ =
      (-1) ^ m / (2 ^ m * (m.factorial : ℚ)) *
        ((2 * m + 2 * r + 2 * δ - 1).doubleFactorial : ℚ) := by
  have h := coeff_iterate_derivative_legendreP (2 * m + δ) r m (by omega)
  rw [show 2 * m + δ - 2 * m = δ by omega,
    show 2 * (2 * m + δ) + 2 * r - 2 * m = 2 * (m + δ + r) by omega,
    show 2 * m + δ + r - m = m + δ + r by omega, Nat.factorial_eq_one.mpr hδ] at h
  rw [h, show 2 * m + 2 * r + 2 * δ - 1 = 2 * (m + δ + r) - 1 by omega]
  have L : ((2 * (m + δ + r)).factorial : ℚ) =
      2 ^ (m + δ + r) * (m + δ + r).factorial * (2 * (m + δ + r) - 1).doubleFactorial := by
    exact_mod_cast factorial_two_mul_eq (m + δ + r)
  rw [L, show 2 * m + δ + r = m + (m + δ + r) by ring, pow_add, one_div_pow, one_div_pow]
  have : ((m + δ + r).factorial : ℚ) ≠ 0 := by positivity
  have : (m.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-- The leading coefficient `[x^n] f = (2n+2r-1)!!/n!` of `f = P_{n+r}^{(r)}`. -/
theorem coeff_iterate_derivative_legendreP_self (n r : ℕ) :
    (derivative^[r] (legendreP (n + r))).coeff n =
      ((2 * n + 2 * r - 1).doubleFactorial : ℚ) / (n.factorial : ℚ) := by
  have h := coeff_iterate_derivative_legendreP n r 0 (Nat.zero_le _)
  simp only [mul_zero, Nat.sub_zero, pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one] at h
  rw [h, show 2 * n + 2 * r = 2 * (n + r) by ring]
  have L : ((2 * (n + r)).factorial : ℚ) =
      2 ^ (n + r) * (n + r).factorial * (2 * (n + r) - 1).doubleFactorial := by
    exact_mod_cast factorial_two_mul_eq (n + r)
  rw [L, one_div_pow]
  have : ((n + r).factorial : ℚ) ≠ 0 := by positivity
  have : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp

theorem coeff_iterate_derivative_legendreP_self_ne_zero (n r : ℕ) :
    (derivative^[r] (legendreP (n + r))).coeff n ≠ 0 := by
  rw [coeff_iterate_derivative_legendreP_self]
  have : ((2 * n + 2 * r - 1).doubleFactorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos _).ne'
  exact div_ne_zero this (by positivity)

/-- `deg P_{n+r}^{(r)} = n`. -/
theorem natDegree_iterate_derivative_legendreP (n r : ℕ) :
    (derivative^[r] (legendreP (n + r))).natDegree = n :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_iterate_derivative_legendreP_le n r)
    (coeff_iterate_derivative_legendreP_self_ne_zero n r)

/-- **The leading coefficient** `lc(f) = (2n+2r-1)!!/n!` of `f = P_{n+r}^{(r)}`. -/
theorem leadingCoeff_iterate_derivative_legendreP (n r : ℕ) :
    (derivative^[r] (legendreP (n + r))).leadingCoeff =
      ((2 * n + 2 * r - 1).doubleFactorial : ℚ) / (n.factorial : ℚ) := by
  rw [leadingCoeff, natDegree_iterate_derivative_legendreP,
    coeff_iterate_derivative_legendreP_self]

/-- **Parity.** `f(-x) = (-1)^n f(x)` for `f = P_{n+r}^{(r)}`. -/
theorem iterate_derivative_legendreP_comp_neg_X (n r : ℕ) :
    (derivative^[r] (legendreP (n + r))).comp (-X) =
      C ((-1) ^ n) * derivative^[r] (legendreP (n + r)) := by
  rw [iterate_derivative_legendreP, mul_comp, C_comp, Polynomial.sum_comp, mul_sum, mul_sum,
    mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hk : k ≤ n / 2 := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [mul_comp, C_comp, X_pow_comp, neg_pow (X : ℚ[X])]
  have : (-1 : ℚ) ^ n = (-1) ^ (n - 2 * k) := by
    have h1 : (-1 : ℚ) ^ n = (-1) ^ (n - 2 * k) * ((-1) ^ 2) ^ k := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    rw [h1]; norm_num
  rw [this]
  simp only [map_pow, map_neg, map_one]
  ring

/-- For `n = 2m+δ`, `δ ∈ {0,1}`, `x^δ` divides `f = P_{n+r}^{(r)}`, so
`f = x^δ (f /ₘ x^δ)`. -/
theorem X_pow_mul_iterate_derivative_legendreP_divByMonic (m r δ : ℕ) (hδ : δ ≤ 1) :
    X ^ δ * (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ X ^ δ) =
      derivative^[r] (legendreP (2 * m + δ + r)) := by
  interval_cases δ
  · simp
  · have h0 : (derivative^[r] (legendreP (2 * m + 1 + r))).coeff 0 = 0 :=
      coeff_iterate_derivative_legendreP_eq_zero_of_odd _ r 0 ⟨m, by ring⟩
    obtain ⟨q, hq⟩ := X_dvd_iff.mpr h0
    rw [pow_one, hq, mul_divByMonic_cancel_left _ monic_X]

/-- **The Gegenbauer equation for `f = P_{n+r}^{(r)}`.**
`(1-x²) f'' - (2r+2) x f' + n(n+2r+1) f = 0`. -/
theorem iterate_derivative_legendreP_differential_equation (n r : ℕ) :
    (1 - X ^ 2) * derivative (derivative (derivative^[r] (legendreP (n + r)))) -
        C (2 * (r : ℚ) + 2) * X * derivative (derivative^[r] (legendreP (n + r))) +
        C ((n : ℚ) * (n + 2 * r + 1)) * derivative^[r] (legendreP (n + r)) = 0 := by
  rw [iterate_derivative_legendreP_eq_gegenbauerC]
  simp only [derivative_C_mul]
  linear_combination C ((2 * r - 1).doubleFactorial : ℚ) * gegenbauerC_differential_equation n r

/-- `P_N(1) = 1`. -/
theorem legendreP_eval_one (N : ℕ) : (legendreP N).eval 1 = 1 := by
  rw [legendreP_eq, jacobiP_eq, eval_mul, eval_C, eval_finsetSum, sum_eq_single 0]
  · simp only [add_zero, Nat.sub_zero, Ring.choose_natCast, Nat.choose_self, Nat.choose_zero_right,
      Nat.cast_one, mul_one, map_one, pow_zero, eval_mul, eval_one, eval_pow, eval_add, eval_X]
    rw [one_mul, show (1 : ℚ) + 1 = 2 by norm_num, ← mul_pow]; norm_num
  · intro j _ hj
    simp [zero_pow hj]
  · intro h; exact absurd (mem_range.mpr (Nat.succ_pos N)) h

/-- **Eq. (3.14), first form.** `f(1) = (n+2r)! / (2^r r! n!)` for `f = P_{n+r}^{(r)}`. -/
theorem eval_one_iterate_derivative_legendreP (n r : ℕ) :
    (derivative^[r] (legendreP (n + r))).eval 1 =
      ((n + 2 * r).factorial : ℚ) / (2 ^ r * (r.factorial : ℚ) * (n.factorial : ℚ)) := by
  induction r generalizing n with
  | zero =>
    simp only [Function.iterate_zero_apply, add_zero, legendreP_eval_one, mul_zero, pow_zero,
      Nat.factorial_zero, Nat.cast_one, one_mul]
    have : (n.factorial : ℚ) ≠ 0 := by positivity
    field_simp
  | succ r ih =>
    have hode := congrArg (eval 1) (iterate_derivative_legendreP_differential_equation (n + 1) r)
    rw [show n + (r + 1) = (n + 1) + r by ring, Function.iterate_succ_apply']
    simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow, eval_one, eval_zero,
      one_pow, sub_self, zero_mul, zero_sub, mul_one] at hode
    rw [ih (n + 1)] at hode
    rw [show n + 1 + 2 * r = (n + 2 * r) + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ n] at hode
    rw [show n + 2 * (r + 1) = (n + 2 * r + 1) + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ (n + 2 * r), Nat.factorial_succ r, pow_succ]
    have h1 : (n.factorial : ℚ) ≠ 0 := by positivity
    have h2 : (r.factorial : ℚ) ≠ 0 := by positivity
    have h3 : ((r : ℚ) + 1) ≠ 0 := by positivity
    have h4 : ((n : ℚ) + 1) ≠ 0 := by positivity
    push_cast at hode ⊢
    field_simp at hode ⊢
    linear_combination (-1 : ℚ) * hode

/-- **Eq. (3.14), second form.** `f(1) = binom(n+2r, 2r) (2r-1)!!`. -/
theorem eval_one_iterate_derivative_legendreP_eq_choose (n r : ℕ) :
    (derivative^[r] (legendreP (n + r))).eval 1 =
      ((n + 2 * r).choose (2 * r) : ℚ) * ((2 * r - 1).doubleFactorial : ℚ) := by
  rw [eval_one_iterate_derivative_legendreP]
  have h1 := Nat.choose_mul_factorial_mul_factorial (n := n + 2 * r) (k := 2 * r) (by omega)
  rw [show n + 2 * r - 2 * r = n by omega] at h1
  have h1' : ((n + 2 * r).choose (2 * r) : ℚ) * ((2 * r).factorial : ℚ) * (n.factorial : ℚ) =
      ((n + 2 * r).factorial : ℚ) := by exact_mod_cast h1
  have h2 : ((2 * r).factorial : ℚ) =
      2 ^ r * r.factorial * (2 * r - 1).doubleFactorial := by
    exact_mod_cast factorial_two_mul_eq r
  rw [← h1', h2]
  have : (n.factorial : ℚ) ≠ 0 := by positivity
  have : (r.factorial : ℚ) ≠ 0 := by positivity
  field_simp

theorem eval_one_iterate_derivative_legendreP_pos (n r : ℕ) :
    0 < (derivative^[r] (legendreP (n + r))).eval 1 := by
  rw [eval_one_iterate_derivative_legendreP]
  exact div_pos (by exact_mod_cast Nat.factorial_pos _) (by positivity)

/-- `f(-1) = (-1)^n f(1)` for `f = P_{n+r}^{(r)}`. -/
theorem eval_neg_one_iterate_derivative_legendreP (n r : ℕ) :
    (derivative^[r] (legendreP (n + r))).eval (-1) =
      (-1) ^ n * (derivative^[r] (legendreP (n + r))).eval 1 := by
  have h := congrArg (eval 1) (iterate_derivative_legendreP_comp_neg_X n r)
  rw [eval_comp, eval_neg, eval_X, eval_mul, eval_C] at h
  exact h

/-- **Eq. (3.14), the other endpoint.** `|f(-1)| = f(1)` for `f = P_{n+r}^{(r)}`. -/
theorem abs_eval_neg_one_iterate_derivative_legendreP (n r : ℕ) :
    |(derivative^[r] (legendreP (n + r))).eval (-1)| =
      (derivative^[r] (legendreP (n + r))).eval 1 := by
  rw [eval_neg_one_iterate_derivative_legendreP, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul, abs_of_pos (eval_one_iterate_derivative_legendreP_pos n r)]

end ArithmeticOfJacobiPolynomials
