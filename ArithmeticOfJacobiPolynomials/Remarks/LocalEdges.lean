/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.KanekoZagierLocal

/-!
# Remark A.4: the Newton edge of the Kaneko–Zagier monic endpoint polynomials

Remark A.4 (`rem:cgl-eisenstein`) compares the monic endpoint polynomial
`n! P_n^{(α,β)}(2X-1)/(n+α+β+1)_n` (`monicEndpoint`, (4.24)) with the polynomials
`S_n^{(λ,μ)}(X-1)` of [CGL]. Its mathematical assertions about the polynomials are:

* for `n = 3^a` (`a ≥ 1`) and `α = λ/3`, `β = μ/2`, the single Newton edge of Theorem A.2 has
  height `(3n-1)/2` (so its height need not be one, as in the Eisenstein criterion):
  `padicValRat_monicEndpoint_coeff_zero_three_pow`;
* `S_3^{(1,1)}(X-1) = X^3 - (63/41) X^2 + (27/41) X - 81/1189`:
  `monicEndpoint_kanekoZagier_three`.

The identification with the notation of [CGL] and the relation with [CGL, Conjecture 1(4)] are
comparisons with the literature and are not formalized.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-- **Remark A.4.** For `n = 3^a` with `a ≥ 1` and `λ, μ ∈ {-1,1}`, the constant coefficient of
the monic endpoint polynomial of `P_n^{(λ/3,μ/2)}` has `3`-adic valuation `(3n-1)/2`: this is the
height of the single Newton edge from `(0, (3n-1)/2)` to `(n, 0)` of Theorem A.2. -/
theorem padicValRat_monicEndpoint_coeff_zero_three_pow {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) (a : ℕ) (ha : 1 ≤ a) :
    padicValRat 3 ((monicEndpoint ((l : ℚ) / 3) ((μ : ℚ) / 2) (3 ^ a)).coeff 0) =
      ((3 * 3 ^ a - 1) / 2 : ℕ) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hα : padicValRat 3 ((l : ℚ) / 3) = -((1 : ℕ) : ℤ) := by
    rw [padicValRat_three_int_div_three hl]; norm_num
  have hβ : 0 ≤ padicValRat 3 ((μ : ℚ) / 2) := (padicValRat_three_int_div_two hμ).symm.le
  have hpoch : padicValRat 3 ((ascPochhammer ℚ (3 ^ a)).eval ((μ : ℚ) / 2 + 1)) =
      padicValNat 3 (3 ^ a).factorial := by
    have hV := padicValNat_factorial_two_mul_prime_pow (p := 3) (by norm_num) a
    rcases hμ with rfl | rfl
    · rw [show ((1 : ℤ) : ℚ) / 2 + 1 = 3 / 2 by norm_num, ascPochhammer_eval_three_halves,
        padicValRat_factorial_div (p := 3) (by norm_num),
        padicValNat_factorial_two_mul_prime_pow_add_one (p := 3) a ha, hV]
      push_cast; ring
    · rw [show ((-1 : ℤ) : ℚ) / 2 + 1 = 1 / 2 by norm_num, ascPochhammer_eval_half,
        padicValRat_factorial_div (p := 3) (by norm_num), hV]
      push_cast; ring
  have h := (primePowerCriterion (p := 3) a ha _ _ 1 one_pos hα hβ hpoch).2.2.2.1
  rw [h, Nat.cast_inj]
  obtain ⟨k, hk⟩ : Odd (3 ^ a) := Odd.pow (by decide)
  rw [hk]
  omega

/-- **Remark A.4.** `S_3^{(1,1)}(X-1)`, the monic endpoint polynomial of `P_3^{(1/3,1/2)}`, is
`X^3 - (63/41) X^2 + (27/41) X - 81/1189`. -/
theorem monicEndpoint_kanekoZagier_three :
    monicEndpoint (1 / 3) (1 / 2) 3 =
      X ^ 3 + C (-63 / 41) * X ^ 2 + C (27 / 41) * X + C (-81 / 1189) := by
  have e3 : ∀ x : ℚ, (ascPochhammer ℚ 3).eval x = x * (x + 1) * (x + 2) := by
    intro x
    rw [show (3 : ℕ) = 0 + 1 + 1 + 1 from rfl, ascPochhammer_succ_eval, ascPochhammer_succ_eval,
      ascPochhammer_succ_eval, ascPochhammer_zero, eval_one]
    push_cast; ring
  have e2 : ∀ x : ℚ, (ascPochhammer ℚ 2).eval x = x * (x + 1) := by
    intro x
    rw [show (2 : ℕ) = 0 + 1 + 1 from rfl, ascPochhammer_succ_eval, ascPochhammer_succ_eval,
      ascPochhammer_zero, eval_one]
    push_cast; ring
  have e1 : ∀ x : ℚ, (ascPochhammer ℚ 1).eval x = x := by
    intro x; rw [ascPochhammer_one, eval_X]
  have e0 : ∀ x : ℚ, (ascPochhammer ℚ 0).eval x = 1 := by
    intro x; rw [ascPochhammer_zero, eval_one]
  have hA : (ascPochhammer ℚ 3).eval (((3 : ℕ) : ℚ) + 1 / 3 + 1 / 2 + 1) ≠ 0 := by
    rw [e3]; norm_num
  rw [monicEndpoint_eq_sum _ _ _ hA]
  apply Polynomial.funext
  intro x
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, monicEndpointCoeff_def,
    Nat.reduceSub, e3, e2, e1, e0, Nat.choose_zero_right, Nat.choose_one_right,
    Nat.choose_two_right, Nat.choose_self]
  norm_num
  all_goals ring

end ArithmeticOfJacobiPolynomials
