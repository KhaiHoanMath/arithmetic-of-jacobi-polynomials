/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Analysis.Margins
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Remark 5.8: the numerical bounds behind Proposition 5.7

Remark 5.8 states that the strict comparisons in the proof of Proposition 5.7 follow from
elementary monotonicity and the bounds
`13.8 < log(10^6) < 13.82`, `log 9 < 2.2`, `log 2 < 0.7`, `(10^6)^{1/4} > 31.6`.
These five bounds are proved here (`log_million_gt`, `log_million_lt`, `log_nine_lt`,
`log_two_lt_seven_tenths`, `million_rpow_quarter_gt`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Real

/-- `log(10^6) = 20 log 2 + log(10^6/2^20)`. -/
theorem log_million_eq :
    log ((10 : ℝ) ^ 6) = 20 * log 2 + log ((10 : ℝ) ^ 6 / 2 ^ 20) := by
  have h := log_mul (x := (2 : ℝ) ^ 20) (y := (10 : ℝ) ^ 6 / 2 ^ 20) (by norm_num) (by norm_num)
  have h20 : log ((2 : ℝ) ^ 20) = 20 * log 2 := by rw [log_pow]; norm_num
  rw [show (2 : ℝ) ^ 20 * ((10 : ℝ) ^ 6 / 2 ^ 20) = 10 ^ 6 by norm_num, h20] at h
  exact h

/-- **Remark 5.8.** `13.8 < log(10^6)`. -/
theorem log_million_gt : (13.8 : ℝ) < log ((10 : ℝ) ^ 6) := by
  have h3 := one_sub_inv_le_log_of_pos (x := (10 : ℝ) ^ 6 / 2 ^ 20) (by norm_num)
  have h4 : (1 : ℝ) - ((10 : ℝ) ^ 6 / 2 ^ 20)⁻¹ = 1 - 1048576 / 1000000 := by norm_num
  rw [h4] at h3
  rw [log_million_eq]
  linarith [log_two_gt_d9]

/-- **Remark 5.8.** `log(10^6) < 13.82`. -/
theorem log_million_lt : log ((10 : ℝ) ^ 6) < 13.82 := by
  have h3 := log_le_sub_one_of_pos (x := (10 : ℝ) ^ 6 / 2 ^ 20) (by norm_num)
  have h4 : (10 : ℝ) ^ 6 / 2 ^ 20 - 1 = 1000000 / 1048576 - 1 := by norm_num
  rw [h4] at h3
  rw [log_million_eq]
  linarith [log_two_lt_d9]

/-- **Remark 5.8.** `log 9 < 2.2`. -/
theorem log_nine_lt : log 9 < (2.2 : ℝ) := by
  have h := log_div_le_two_mul_sum_add (z := 1 / 17) (by norm_num) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h
  have h98 : log (9 / 8) = log 9 - log 8 := log_div (by norm_num) (by norm_num)
  have h8 : log 8 = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]; norm_num
  linarith [log_two_lt_d9]

/-- **Remark 5.8.** `log 2 < 0.7`. -/
theorem log_two_lt_seven_tenths : log 2 < (0.7 : ℝ) := by
  linarith [log_two_lt_d9]

/-- **Remark 5.8.** `(10^6)^{1/4} > 31.6`. -/
theorem million_rpow_quarter_gt : (31.6 : ℝ) < ((10 : ℝ) ^ 6) ^ (1 / 4 : ℝ) := by
  have h : (31.6 : ℝ) = ((31.6 : ℝ) ^ 4) ^ (1 / 4 : ℝ) := by
    rw [← rpow_natCast, ← rpow_mul (by norm_num)]
    norm_num
  rw [h]
  exact rpow_lt_rpow (by positivity) (by norm_num) (by norm_num)

end ArithmeticOfJacobiPolynomials
