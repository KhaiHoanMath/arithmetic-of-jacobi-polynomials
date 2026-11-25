/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.CentralValue
public import ArithmeticOfJacobiPolynomials.Jacobi.SymmetricCriterion
public import ArithmeticOfJacobiPolynomials.Padic.IntegralLocalBound
public import Mathlib.Tactic.NormNum.Prime

/-!
# Worked examples stated in the prose of the manuscript

* §3.1, after Lemma 3.2: for `(a,b) = (1,0)` the central-value formulas reduce to
  `A_0 = D_0 = 1`, `A_1(z) = 2z + 1`, `D_1(z) = 2(z+1)`, so the central value never vanishes
  (`centralA_one_zero_zero`, `centralD_one_zero_zero`, `centralA_one_zero_one`,
  `centralD_one_zero_one`, `jacobiP_one_zero_eval_zero_ne_zero`).
* §3.2, after (3.14): although `A ≤ 1`, the truncated product `A_{≤m}` need not be at most `1`;
  for `r = 1`, `m = 4`, `δ = 0` one has `A = 9/10` and `A_{≤m} = 9/2`
  (`symmetricRatio_eight_one`, `primeTruncation_symmetricRatio_eight_one`).
* §6.6 (further questions): all-degree irreducibility fails for some fixed `r`, since
  `C_2^{7/2}(x) = (7/2)(3x-1)(3x+1)` (`gegenbauerC_seven_halves_two`,
  `not_irreducible_reducedGegenbauer_one_three_zero`).
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-! ### The central-value polynomials for `(a,b) = (1,0)` -/

/-- `A_0 = 1` for `(a,b) = (1,0)`. -/
theorem centralA_one_zero_zero : centralA 1 0 0 = 1 := by
  have hH : centralH 1 0 0 = 0 := by simp [centralH_eq]
  have hK : centralK 1 0 0 = 0 := by simp [centralK_eq, hH]
  rw [centralA_eq, hH, hK]
  simp

/-- `D_0 = 1` for `(a,b) = (1,0)`. -/
theorem centralD_one_zero_zero : centralD 1 0 0 = 1 := by
  have hH : centralH 1 0 0 = 0 := by simp [centralH_eq]
  have hK : centralK 1 0 0 = 0 := by simp [centralK_eq, hH]
  rw [centralD_eq, hK]
  simp

/-- `A_1(z) = 2z + 1` for `(a,b) = (1,0)`. -/
theorem centralA_one_zero_one : centralA 1 0 1 = C 2 * polyX + C 1 := by
  have hH : centralH 1 0 1 = 0 := by simp [centralH_eq]
  have hK : centralK 1 0 1 = 1 := by simp [centralK_eq, hH]
  rw [centralA_eq, hH, hK]
  simp

/-- `D_1(z) = 2(z+1)` for `(a,b) = (1,0)`. -/
theorem centralD_one_zero_one : centralD 1 0 1 = C 2 * (polyX + C 1) := by
  have hH : centralH 1 0 1 = 0 := by simp [centralH_eq]
  have hK : centralK 1 0 1 = 1 := by simp [centralK_eq, hH]
  rw [centralD_eq, hK]
  simp

/-- For `(a,b) = (1,0)` the central value `P_n^{(1,0)}(0)` never vanishes, in either parity. -/
theorem jacobiP_one_zero_eval_zero_ne_zero (n : ℕ) : (jacobiP 1 0 n).eval 0 ≠ 0 := by
  obtain ⟨m, δ, hδ, rfl⟩ : ∃ m δ, δ ≤ 1 ∧ n = 2 * m + δ := ⟨n / 2, n % 2, by omega, by omega⟩
  have h := jacobiP_eval_zero_eq_central 1 0 m δ (by norm_num) hδ
  rw [Nat.cast_one, Nat.cast_zero] at h
  rw [h]
  have hA : (((centralA 1 0 δ).eval (m : ℤ) : ℤ) : ℚ) ≠ 0 := by
    interval_cases δ
    · rw [centralA_one_zero_zero]; simp
    · rw [centralA_one_zero_one]
      simp only [eval_add, eval_mul, eval_C, eval_X]
      push_cast
      positivity
  have hD := (centralD_eval_pos 1 0 δ m).ne'
  have hc : ((2 * m).choose m : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  refine div_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) hA) hD
  · exact pow_ne_zero _ (by norm_num)
  · exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hc

/-! ### The truncated factorial ratio for `r = 1`, `m = 4`, `δ = 0` -/

/-- For `r = 1`, `m = 4`, `δ = 0` (so `n = 8`), `A = (n+r)!²/(n!(n+2r)!) = 9/10`. -/
theorem symmetricRatio_eight_one : symmetricRatio 8 1 = 9 / 10 := by
  rw [symmetricRatio_eq, show 8 + 2 * 1 = 8 + 1 + 1 from rfl, Nat.factorial_succ (8 + 1),
    Nat.factorial_succ 8]
  push_cast
  rw [div_eq_iff (by positivity)]
  ring

/-- For `r = 1`, `m = 4`, `δ = 0`, the truncated product `A_{≤m} = ∏_{p ≤ m} p^{v_p(A)}`
equals `9/2`. -/
theorem primeTruncation_symmetricRatio_eight_one :
    primeTruncation (symmetricRatio 8 1) 4 = 9 / 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have e : (9 / 10 : ℚ) = ((9 : ℕ) : ℚ) / ((10 : ℕ) : ℚ) := by norm_num
  have h2 : padicValRat 2 (9 / 10 : ℚ) = -1 := by
    rw [e, padicValRat.div (by norm_num) (by norm_num), padicValRat.of_nat, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 9),
      show (10 : ℕ) = 2 * 5 from rfl, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat_self, padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 5)]
    norm_num
  have h3 : padicValRat 3 (9 / 10 : ℚ) = 2 := by
    rw [e, padicValRat.div (by norm_num) (by norm_num), padicValRat.of_nat, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 10),
      show (9 : ℕ) = 3 ^ 2 from rfl, padicValNat.prime_pow]
    norm_num
  have h4 : ¬ Nat.Prime 4 := fun h => by
    have := h.eq_one_or_self_of_dvd 2 (by norm_num)
    omega
  rw [primeTruncation_eq, symmetricRatio_eight_one, prod_filter]
  simp only [prod_range_succ, prod_range_zero, one_mul]
  simp only [Nat.not_prime_zero, Nat.not_prime_one, Nat.prime_two, Nat.prime_three, h4,
    ↓reduceIte, h2, h3]
  norm_num [zpow_neg, zpow_one]

/-- The example of §3.2: `A ≤ 1` while `A_{≤m} > 1` (`r = 1`, `m = 4`, `δ = 0`). -/
theorem symmetricRatio_le_one_lt_primeTruncation_eight_one :
    symmetricRatio 8 1 ≤ 1 ∧ 1 < primeTruncation (symmetricRatio 8 1) 4 := by
  rw [primeTruncation_symmetricRatio_eight_one, symmetricRatio_eight_one]
  norm_num

/-! ### A reducible Gegenbauer polynomial -/

/-- `C_2^{7/2}(x) = (7/2)(3x-1)(3x+1)`. -/
theorem gegenbauerC_seven_halves_two :
    gegenbauerC (7 / 2) 2 = C (7 / 2) * (C 3 * polyX - 1) * (C 3 * polyX + 1) := by
  have h2 : (ascPochhammer ℚ 2).eval (7 / 2 : ℚ) = 63 / 4 := by
    rw [show (2 : ℕ) = 0 + 1 + 1 from rfl, ascPochhammer_succ_eval, ascPochhammer_succ_eval,
      ascPochhammer_zero, eval_one]
    norm_num
  have h1 : (ascPochhammer ℚ 1).eval (7 / 2 : ℚ) = 7 / 2 := by
    rw [ascPochhammer_one, eval_X]
  apply Polynomial.funext
  intro x
  rw [gegenbauerC_eq]
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_add, eval_one, Nat.reduceDiv,
    Nat.reduceAdd, sum_range_succ, sum_range_zero, zero_add, Nat.reduceMul, Nat.reduceSub, h1, h2,
    Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two]
  norm_num
  all_goals ring

/-- `F_{1,3,0} = C_2^{7/2}` is reducible over `ℚ`: all-degree irreducibility fails for `r = 3`. -/
theorem not_irreducible_reducedGegenbauer_one_three_zero :
    ¬ Irreducible (reducedGegenbauer 1 3 0) := by
  have e : reducedGegenbauer 1 3 0 = (C (7 / 2) * (C 3 * polyX - 1)) * (C 3 * polyX + 1) := by
    rw [reducedGegenbauer_eq, pow_zero, divByMonic_one,
      show ((3 : ℕ) : ℚ) + 1 / 2 = 7 / 2 by norm_num, show 2 * 1 + 0 = 2 from rfl,
      gegenbauerC_seven_halves_two]
  have d1 : (C (3 : ℚ) * polyX - 1).natDegree = 1 := by
    rw [show (C (3 : ℚ) * polyX - 1) = C 3 * polyX + C (-1) by simp [sub_eq_add_neg]]
    exact natDegree_linear (by norm_num)
  have d2 : (C (3 : ℚ) * polyX + 1).natDegree = 1 := by
    rw [show (C (3 : ℚ) * polyX + 1) = C 3 * polyX + C 1 by simp]
    exact natDegree_linear (by norm_num)
  rw [e]
  intro h
  rcases h.isUnit_or_isUnit rfl with hu | hu
  · have := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_C_mul (by norm_num), d1] at this
    exact one_ne_zero this
  · have := natDegree_eq_zero_of_isUnit hu
    rw [d2] at this
    exact one_ne_zero this

end ArithmeticOfJacobiPolynomials
