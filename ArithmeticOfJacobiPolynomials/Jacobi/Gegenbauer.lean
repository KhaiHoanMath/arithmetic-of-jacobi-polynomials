/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.Legendre
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Derivatives of Legendre polynomials and Gegenbauer polynomials

We prove the coefficient formula (3.10) of the manuscript for `f = P_{n+r}^{(r)}`,
`f(x) = 2^{-n-r} ∑_{k ≤ n/2} (-1)^k (2n+2r-2k)! / (k! (n+r-k)! (n-2k)!) x^{n-2k}`,
and the identity (1.3), `dʳ/dxʳ P_{n+r} = (2r-1)!! C_n^{r+1/2}`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-- `(2t+1)!! = (2t+1) (2t-1)!!`, with `(-1)!! = 0!! = 1` in truncated subtraction. -/
theorem doubleFactorial_two_mul_add_one (t : ℕ) :
    (2 * t + 1).doubleFactorial = (2 * t + 1) * (2 * t - 1).doubleFactorial := by
  cases t with
  | zero => rfl
  | succ t =>
    rw [show 2 * (t + 1) + 1 = (2 * t + 1) + 2 by ring, Nat.doubleFactorial_add_two,
      show 2 * (t + 1) - 1 = 2 * t + 1 by omega]

/-- `(2t)! = 2^t t! (2t-1)!!`. -/
theorem factorial_two_mul_eq (t : ℕ) :
    (2 * t).factorial = 2 ^ t * t.factorial * (2 * t - 1).doubleFactorial := by
  cases t with
  | zero => rfl
  | succ t =>
    rw [show 2 * (t + 1) = (2 * t + 1) + 1 by ring, Nat.factorial_eq_mul_doubleFactorial,
      show 2 * t + 1 + 1 = 2 * (t + 1) by ring, Nat.doubleFactorial_two_mul,
      show 2 * (t + 1) - 1 = 2 * t + 1 by omega]

/-- `(2r-1)!! (r+1/2)_M 2^M = (2(r+M)-1)!!`. -/
theorem doubleFactorial_mul_ascPochhammer_eval (r M : ℕ) :
    ((2 * r - 1).doubleFactorial : ℚ) * (ascPochhammer ℚ M).eval ((r : ℚ) + 1 / 2) * 2 ^ M =
      ((2 * (r + M) - 1).doubleFactorial : ℚ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [ascPochhammer_succ_eval, show 2 * (r + (M + 1)) - 1 = 2 * (r + M) + 1 by omega,
      doubleFactorial_two_mul_add_one]
    push_cast
    rw [← ih]
    ring

/-- **Eq. (3.10).** The coefficient formula for `f = P_{n+r}^{(r)}`:
`f(x) = 2^{-n-r} ∑_{k ≤ n/2} (-1)^k (2n+2r-2k)! / (k! (n+r-k)! (n-2k)!) x^{n-2k}`. -/
theorem iterate_derivative_legendreP (n r : ℕ) :
    derivative^[r] (legendreP (n + r)) = C ((1 / 2 : ℚ) ^ (n + r)) *
      ∑ k ∈ range (n / 2 + 1),
        C ((-1) ^ k * ((2 * n + 2 * r - 2 * k).factorial : ℚ) /
          ((k.factorial : ℚ) * ((n + r - k).factorial : ℚ) * ((n - 2 * k).factorial : ℚ))) *
          X ^ (n - 2 * k) := by
  rw [legendreP_explicit, iterate_derivative_C_mul, iterate_derivative_sum, one_div_pow]
  congr 1
  have hsub : range (n / 2 + 1) ⊆ range ((n + r) / 2 + 1) := fun k hk => by
    simp only [mem_range] at hk ⊢; omega
  rw [← sum_subset hsub]
  · refine sum_congr rfl fun k hk => ?_
    have hk : 2 * k ≤ n := by have := mem_range.mp hk; omega
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul, ← mul_assoc, ← C_mul,
      show 2 * k + a + r - 2 * k - r = 2 * k + a - 2 * k by omega,
      show 2 * (2 * k + a + r) - 2 * k = 2 * k + 2 * a + 2 * r by omega,
      show 2 * (2 * k + a) + 2 * r - 2 * k = 2 * k + 2 * a + 2 * r by omega,
      show 2 * k + a + r - 2 * k = a + r by omega,
      show 2 * k + a + r - k = k + a + r by omega,
      show 2 * k + a - 2 * k = a by omega]
    congr 2
    have h1 := Nat.choose_mul_factorial_mul_factorial (n := 2 * k + a + r) (k := k) (by omega)
    rw [show 2 * k + a + r - k = k + a + r by omega] at h1
    have h2 := Nat.choose_mul_factorial_mul_factorial (n := 2 * k + 2 * a + 2 * r)
      (k := 2 * k + a + r) (by omega)
    rw [show 2 * k + 2 * a + 2 * r - (2 * k + a + r) = a + r by omega] at h2
    have h3 := Nat.factorial_mul_descFactorial (n := a + r) (k := r) (by omega)
    rw [show a + r - r = a by omega] at h3
    have h1' : ((2 * k + a + r).choose k : ℚ) * k.factorial * (k + a + r).factorial =
        (2 * k + a + r).factorial := by exact_mod_cast h1
    have h2' : ((2 * k + 2 * a + 2 * r).choose (2 * k + a + r) : ℚ) *
        (2 * k + a + r).factorial * (a + r).factorial = (2 * k + 2 * a + 2 * r).factorial := by
      exact_mod_cast h2
    have h3' : (a.factorial : ℚ) * (a + r).descFactorial r = (a + r).factorial := by
      exact_mod_cast h3
    rw [eq_div_iff (by positivity)]
    linear_combination (-1 : ℚ) ^ k * (h2' +
      ((2 * k + 2 * a + 2 * r).choose (2 * k + a + r) : ℚ) * (2 * k + a + r).factorial * h3' +
      ((2 * k + 2 * a + 2 * r).choose (2 * k + a + r) : ℚ) * (a + r).descFactorial r *
        a.factorial * h1')
  · intro k hk' hk
    have hk : n / 2 < k := by simpa using hk
    have hk' := mem_range.mp hk'
    rw [iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul,
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
    simp

/-- **Eq. (1.3).** `dʳ/dxʳ P_{n+r}(x) = (2r-1)!! C_n^{r+1/2}(x)`, where `(2·0-1)!! = 1`. -/
theorem iterate_derivative_legendreP_eq_gegenbauerC (n r : ℕ) :
    derivative^[r] (legendreP (n + r)) =
      C ((2 * r - 1).doubleFactorial : ℚ) * gegenbauerC ((r : ℚ) + 1 / 2) n := by
  rw [iterate_derivative_legendreP, gegenbauerC_eq, mul_sum, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hk : 2 * k ≤ n := by have := mem_range.mp hk; omega
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul,
    show 2 * (2 * k + a) + 2 * r - 2 * k = 2 * (k + a + r) by omega,
    show 2 * k + a + r - k = k + a + r by omega,
    show 2 * k + a - 2 * k = a by omega,
    show 2 * k + a - k = k + a by omega]
  congr 2
  have L1 := doubleFactorial_mul_ascPochhammer_eval r (k + a)
  rw [show r + (k + a) = k + a + r by ring] at L1
  have L2 : ((2 * (k + a + r)).factorial : ℚ) =
      2 ^ (k + a + r) * (k + a + r).factorial * (2 * (k + a + r) - 1).doubleFactorial := by
    exact_mod_cast factorial_two_mul_eq (k + a + r)
  have hD : ((2 * r - 1).doubleFactorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos _).ne'
  have hasc : (ascPochhammer ℚ (k + a)).eval ((r : ℚ) + 1 / 2) =
      ((2 * (k + a + r) - 1).doubleFactorial : ℚ) /
        (((2 * r - 1).doubleFactorial : ℚ) * 2 ^ (k + a)) := by
    rw [eq_div_iff (by positivity)]
    linear_combination L1
  rw [hasc, L2, one_div_pow]
  field_simp
  ring

/-- The differentiated Rodrigues relation: for `u = (x²-1)^N`,
`(x²-1) u^{(m+2)} + (2(m+1)-2N) x u^{(m+1)} + ((m+1)m - 2N(m+1)) u^{(m)} = 0`. -/
theorem X_sq_sub_one_pow_iterate_derivative_relation (N m : ℕ) :
    (X ^ 2 - 1) * derivative^[m + 2] ((X ^ 2 - 1 : ℚ[X]) ^ N) +
        (2 * ((m : ℚ[X]) + 1) - 2 * (N : ℚ[X])) * X *
          derivative^[m + 1] ((X ^ 2 - 1 : ℚ[X]) ^ N) +
        (((m : ℚ[X]) + 1) * (m : ℚ[X]) - 2 * (N : ℚ[X]) * ((m : ℚ[X]) + 1)) *
          derivative^[m] ((X ^ 2 - 1 : ℚ[X]) ^ N) =
      0 := by
  set u : ℚ[X] := (X ^ 2 - 1) ^ N
  have h0 : (X ^ 2 - 1) * derivative u - 2 * (N : ℚ[X]) * X * u = 0 := by
    simp only [u]
    cases N with
    | zero => simp
    | succ N =>
      rw [derivative_pow, Nat.add_sub_cancel, derivative_sub, derivative_X_sq, derivative_one,
        pow_succ]
      simp only [map_ofNat, map_natCast]
      push_cast
      ring
  induction m with
  | zero =>
    have := congrArg derivative h0
    simp only [derivative_mul, derivative_sub, derivative_X_sq, derivative_one,
      derivative_natCast, derivative_ofNat, derivative_X, derivative_zero, map_ofNat] at this
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, zero_add,
      Nat.cast_zero]
    linear_combination this
  | succ m ih =>
    have := congrArg derivative ih
    simp only [derivative_mul, derivative_add, derivative_sub, derivative_X_sq, derivative_one,
      derivative_natCast, derivative_ofNat, derivative_X, derivative_zero, map_ofNat] at this
    simp only [Function.iterate_succ_apply'] at this ⊢
    push_cast
    linear_combination this

/-- **The Gegenbauer differential equation** for `f = C_n^{r+1/2}`:
`(1-x²) f'' - (2r+2) x f' + n(n+2r+1) f = 0`. -/
theorem gegenbauerC_differential_equation (n r : ℕ) :
    (1 - X ^ 2) * derivative (derivative (gegenbauerC ((r : ℚ) + 1 / 2) n)) -
        C (2 * (r : ℚ) + 2) * X * derivative (gegenbauerC ((r : ℚ) + 1 / 2) n) +
        C ((n : ℚ) * (n + 2 * r + 1)) * gegenbauerC ((r : ℚ) + 1 / 2) n = 0 := by
  set f := gegenbauerC ((r : ℚ) + 1 / 2) n
  set u : ℚ[X] := (X ^ 2 - 1) ^ (n + r)
  have hc : (1 / (2 ^ (n + r) * ((n + r).factorial : ℚ))) ≠ 0 := by
    have : ((n + r).factorial : ℚ) ≠ 0 := by positivity
    exact one_div_ne_zero (mul_ne_zero (pow_ne_zero _ two_ne_zero) this)
  have hd : ((2 * r - 1).doubleFactorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos _).ne'
  set c : ℚ := 1 / (2 ^ (n + r) * ((n + r).factorial : ℚ))
  set d : ℚ := ((2 * r - 1).doubleFactorial : ℚ)
  have hg : derivative^[n + 2 * r] u = C (d / c) * f := by
    have h := iterate_derivative_legendreP_eq_gegenbauerC n r
    rw [legendreP_eq_rodrigues, iterate_derivative_C_mul, ← Function.iterate_add_apply,
      show r + (n + r) = n + 2 * r by ring] at h
    have : C (d / c) = C c⁻¹ * C d := by rw [← C_mul]; congr 1; field_simp
    rw [this, mul_assoc, ← h, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul]
  have H := X_sq_sub_one_pow_iterate_derivative_relation (n + r) (n + 2 * r)
  rw [show n + 2 * r + 2 = (n + 2 * r + 1) + 1 by ring, Function.iterate_succ_apply',
    Function.iterate_succ_apply', hg] at H
  simp only [derivative_mul, derivative_C, zero_mul, zero_add] at H
  have hK : C (d / c) ≠ 0 := by
    rw [Ne, C_eq_zero]; exact div_ne_zero hd hc
  have e1 : C (2 * (r : ℚ) + 2) = 2 * (r : ℚ[X]) + 2 := by
    simp only [map_add, map_mul, map_ofNat, map_natCast]
  have e2 : C ((n : ℚ) * (n + 2 * r + 1)) =
      (n : ℚ[X]) * ((n : ℚ[X]) + 2 * (r : ℚ[X]) + 1) := by
    simp only [map_add, map_mul, map_ofNat, map_natCast, map_one]
  rw [e1, e2]
  push_cast at H
  have : C (d / c) * ((1 - X ^ 2) * derivative (derivative f) -
      (2 * (r : ℚ[X]) + 2) * X * derivative f +
        (n : ℚ[X]) * ((n : ℚ[X]) + 2 * (r : ℚ[X]) + 1) * f) = 0 := by
    linear_combination (-1 : ℚ[X]) * H
  exact (mul_eq_zero.mp this).resolve_left hK

end ArithmeticOfJacobiPolynomials
