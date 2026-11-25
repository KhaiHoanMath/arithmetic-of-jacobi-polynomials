/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.Shift
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.ComputeDegree

/-!
# Endpoint values, degree and leading coefficient of Jacobi polynomials

Eq. (5.5) of the manuscript (§5.1):
`P_n^{(α,β)}(1) = binom(n+α, n)` and `P_n^{(α,β)}(-1) = (-1)^n binom(n+β, n)`.
We also record `deg P_n^{(α,β)} ≤ n`, the coefficient of `X^n`, namely
`2^{-n} binom(2n+α+β, n)`, and hence `deg P_n^{(α,β)} = n` when this binomial is nonzero.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-- The endpoint value `P_n^{(α,β)}(1) = binom(n+α, n)` of (5.5). -/
theorem jacobiP_eval_one (α β : ℚ) (n : ℕ) :
    (jacobiP α β n).eval 1 = Ring.choose ((n : ℚ) + α) n := by
  have h1 : (jacobiP α β n).eval 1 = ((jacobiP α β n).comp (2 * X + 1)).coeff 0 := by
    rw [coeff_zero_eq_eval_zero, eval_comp]; simp
  rw [h1, jacobiP_comp_two_mul_X_add_one, finsetSum_coeff]
  simp

/-- The endpoint value `P_n^{(α,β)}(-1) = (-1)^n binom(n+β, n)` of (5.5). -/
theorem jacobiP_eval_neg_one (α β : ℚ) (n : ℕ) :
    (jacobiP α β n).eval (-1) = (-1) ^ n * Ring.choose ((n : ℚ) + β) n := by
  have h := congrArg (eval 1) (jacobiP_comp_neg_X β α n)
  rw [eval_comp, eval_mul, eval_C, jacobiP_eval_one] at h
  simpa using h

/-- `deg P_n^{(α,β)} ≤ n`. -/
theorem natDegree_jacobiP_le (α β : ℚ) (n : ℕ) : (jacobiP α β n).natDegree ≤ n := by
  rw [jacobiP_eq]
  refine (natDegree_C_mul_le _ _).trans ?_
  refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  refine natDegree_mul_le.trans ?_
  have h1 : (C (Ring.choose ((n : ℚ) + α) (n - j) * Ring.choose ((n : ℚ) + β) j) *
      (X - 1) ^ j : ℚ[X]).natDegree ≤ j := by
    refine (natDegree_C_mul_le _ _).trans ?_
    have : ((X - 1 : ℚ[X])).natDegree ≤ 1 := by compute_degree
    simpa using natDegree_pow_le_of_le j this
  have h2 : ((X + 1) ^ (n - j) : ℚ[X]).natDegree ≤ n - j := by
    simp
  omega

/-- For `deg q ≤ n`, the coefficient of `X^n` in `q(2X+1)` is `2^n` times that of `q`. -/
private lemma coeff_comp_two_mul_X_add_one {q : ℚ[X]} {n : ℕ} (hq : q.natDegree ≤ n) :
    (q.comp (2 * X + 1)).coeff n = 2 ^ n * q.coeff n := by
  have hlin : (2 * X + 1 : ℚ[X]) = C 2 * X + C 1 := by simp [C_ofNat]
  have hdeg : (2 * X + 1 : ℚ[X]).natDegree = 1 := by
    rw [hlin]; exact natDegree_linear two_ne_zero
  rcases hq.lt_or_eq with hlt | heq
  · rw [coeff_eq_zero_of_natDegree_lt hlt, mul_zero]
    refine coeff_eq_zero_of_natDegree_lt (natDegree_comp_le.trans_lt ?_)
    rw [hdeg, mul_one]; exact hlt
  · have h := coeff_comp_degree_mul_degree (p := q) (q := (2 * X + 1 : ℚ[X]))
      (by rw [hdeg]; exact one_ne_zero)
    rw [hdeg, mul_one, heq] at h
    rw [h, ← heq, leadingCoeff, coeff_natDegree, hlin, leadingCoeff_linear two_ne_zero]
    ring

/-- The coefficient of `X^n` in `P_n^{(α,β)}` is `2^{-n} binom(2n+α+β, n)`. -/
theorem coeff_jacobiP_self (α β : ℚ) (n : ℕ) :
    (jacobiP α β n).coeff n = (1 / 2 : ℚ) ^ n * Ring.choose (2 * (n : ℚ) + α + β) n := by
  have h := coeff_comp_two_mul_X_add_one (natDegree_jacobiP_le α β n)
  rw [jacobiP_comp_two_mul_X_add_one, finsetSum_coeff] at h
  simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq, mem_range, Nat.lt_succ_self, ite_true,
    Nat.sub_self, Ring.choose_zero_right, one_mul] at h
  have e : (n : ℚ) + α + β + n = 2 * n + α + β := by ring
  rw [e] at h
  rw [h, ← mul_assoc, ← mul_pow]
  norm_num

/-- `deg P_n^{(α,β)} = n` when `binom(2n+α+β, n) ≠ 0`. -/
theorem natDegree_jacobiP (α β : ℚ) (n : ℕ) (h : Ring.choose (2 * (n : ℚ) + α + β) n ≠ 0) :
    (jacobiP α β n).natDegree = n := by
  refine le_antisymm (natDegree_jacobiP_le α β n) (le_natDegree_of_ne_zero ?_)
  rw [coeff_jacobiP_self]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) h

/-- The leading coefficient `2^{-n} binom(2n+α+β, n)` of `P_n^{(α,β)}`, when it is nonzero. -/
theorem leadingCoeff_jacobiP (α β : ℚ) (n : ℕ) (h : Ring.choose (2 * (n : ℚ) + α + β) n ≠ 0) :
    (jacobiP α β n).leadingCoeff = (1 / 2 : ℚ) ^ n * Ring.choose (2 * (n : ℚ) + α + β) n := by
  rw [leadingCoeff, natDegree_jacobiP α β n h, coeff_jacobiP_self]

end ArithmeticOfJacobiPolynomials
