/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Analysis.Margins
public import ArithmeticOfJacobiPolynomials.NumberTheory.LcmBound
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# Numerical ranges for the symmetric criterion

Section 3.2 of the manuscript. For integers `r ≥ 0`, `m ≥ 1`, `δ ∈ {0,1}`, put `n = 2m+δ`,
`S = 2n+2r+1`, `M = m+r`, `K = binom(m+r, r)`, `B = binom(n+r, r)`.

* `symmetric_elementary_of_range`: the explicit assertion of Theorem 1.4, i.e. the elementary
  criterion (3.6) holds whenever `m ≥ max{100r, 1000}`.
* `first_derivative_range`, `first_derivative_exact_criterion`: the case `r = 1`, `m ≥ 200`, in the
  proof of Theorem 1.5, and the resulting form of the exact criterion (3.5).
* `legendre_range`, `legendre_exact_criterion`: the case `r = 0`, `m ≥ 100`.

The arguments follow the manuscript: `binom(u, v) ≤ (eu/v)^v`, monotonicity in `r` (here through
the concavity of `log`, in the form of Bernoulli's inequality), monotonicity in `m` (here through
`log x ≤ log a + x/a - 1`), and `log(4/3) > 2/7` (here `log(4/3) > 0.2876`, from the series of
`2 artanh(1/7)`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Real

/-! ### Numerical constants -/

theorem log_three_lt_d4 : log 3 < (1.0987 : ℝ) := by
  have h := log_div_le_two_mul_sum_add (z := 1 / 5) (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h
  have h32 : log (3 / 2) = log 3 - log 2 := Real.log_div (by norm_num) (by norm_num)
  linarith [Real.log_two_lt_d9]

theorem log_four_div_three_gt : (0.2876 : ℝ) < log (4 / 3) := by
  have h := two_mul_sum_le_log_div (z := 1 / 7) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem log_four_eq_log_three_add (x : ℝ) : x * log 4 = x * log 3 + x * log (4 / 3) := by
  rw [Real.log_div (by norm_num) (by norm_num)]
  ring

/-! ### Elementary estimates -/

/-- `log x ≤ log a + x / a - 1` for `x, a > 0`. -/
theorem log_le_log_add_div_sub_one {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    log x ≤ log a + x / a - 1 := by
  have := Real.log_le_sub_one_of_pos (div_pos hx ha)
  rw [Real.log_div hx.ne' ha.ne'] at this
  linarith

/-- `log x ≤ k log 2 + x / 2^k - 1` for `x > 0`. -/
theorem log_le_mul_log_two_add {x : ℝ} (hx : 0 < x) (k : ℕ) :
    log x ≤ k * log 2 + x / 2 ^ k - 1 := by
  have := log_le_log_add_div_sub_one hx (by positivity : (0 : ℝ) < 2 ^ k)
  rwa [Real.log_pow] at this

/-- `log(8√x) ≤ 3 log 2 + (k log 2 + x / 2^k - 1) / 2` for `x > 0`. -/
theorem log_eight_mul_sqrt_le {x : ℝ} (hx : 0 < x) (k : ℕ) :
    log (8 * √x) ≤ 3 * log 2 + (k * log 2 + x / 2 ^ k - 1) / 2 := by
  have h8 : log (8 : ℝ) = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  rw [Real.log_mul (by norm_num) (Real.sqrt_pos.mpr hx).ne', Real.log_sqrt hx.le, h8]
  have := log_le_mul_log_two_add hx k
  linarith

theorem sqrt_le_of_le_sq {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y ^ 2) : √x ≤ y :=
  (Real.sqrt_le_sqrt h).trans (Real.sqrt_sq hy).le

/-- `binom(a+r, r) ≤ (e(a+r)/r)^r`, in logarithmic form. -/
theorem log_choose_add_le (a r : ℕ) (hr : 0 < r) :
    log ((a + r).choose r : ℝ) ≤ r + r * log (1 + a / r) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hC : (0 : ℝ) < ((a + r).choose r : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have h1 : ((a + r).choose r : ℝ) ≤ ((a + r : ℕ) : ℝ) ^ r / (r.factorial : ℝ) :=
    Nat.choose_le_pow_div r (a + r)
  have h2 : (r : ℝ) ^ r / (r.factorial : ℝ) ≤ exp r := Real.pow_div_factorial_le_exp _ hr'.le r
  have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have h3 : ((a + r : ℕ) : ℝ) ^ r / (r.factorial : ℝ) =
      (1 + a / r) ^ r * ((r : ℝ) ^ r / r.factorial) := by
    rw [← mul_div_assoc, ← mul_pow]
    congr 2
    push_cast
    field_simp
    ring
  have h4 : ((a + r).choose r : ℝ) ≤ (1 + a / r) ^ r * exp r := by
    rw [h3] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have := Real.log_le_log hC h4
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_pow, Real.log_exp] at this
  linarith

/-- Concavity of `log`: `l log(1 + c/l) ≤ log(1 + c)` for `0 < l ≤ 1`, `c ≥ 0`. -/
theorem mul_log_one_add_div_le {l c : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) (hc : 0 ≤ c) :
    l * log (1 + c / l) ≤ log (1 + c) := by
  have hs : (-1 : ℝ) ≤ c / l := by
    have : 0 ≤ c / l := div_nonneg hc hl0.le
    linarith
  have h := rpow_one_add_le_one_add_mul_self hs hl0.le hl1
  have hcl : l * (c / l) = c := by field_simp
  rw [hcl] at h
  have hpos : 0 < 1 + c / l := by positivity
  have := Real.log_le_log (Real.rpow_pos_of_pos hpos l) h
  rwa [Real.log_rpow hpos] at this

/-- Monotonicity in `r`: for `0 < r ≤ m / 100` and `a ≥ 0`,
`r log(1 + a/r) ≤ (m/100) log(1 + 100a/m)`. -/
theorem mul_log_one_add_div_le_of_le {a r m : ℝ} (hr : 0 < r) (hrm : 100 * r ≤ m) (ha : 0 ≤ a) :
    r * log (1 + a / r) ≤ m / 100 * log (1 + 100 * a / m) := by
  have hm : 0 < m := by linarith
  have hl0 : 0 < 100 * r / m := by positivity
  have hl1 : 100 * r / m ≤ 1 := (div_le_one hm).mpr hrm
  have h := mul_log_one_add_div_le hl0 hl1 (c := 100 * a / m) (by positivity)
  have he : 100 * a / m / (100 * r / m) = a / r := by field_simp
  rw [he] at h
  have : r * log (1 + a / r) = m / 100 * (100 * r / m * log (1 + a / r)) := by field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- For `m ≥ max{100r, 1000}` and `n ≤ 2m+1`: `log K + 2 log B < 0.1824 m`, where
`K = binom(m+r, r)` and `B = binom(n+r, r)`. -/
theorem log_choose_add_two_mul_log_choose_le (r m n : ℕ) (hrm : 100 * r ≤ m) (hm : 1000 ≤ m)
    (hn : n ≤ 2 * m + 1) :
    log ((m + r).choose r : ℝ) + 2 * log ((n + r).choose r : ℝ) < 0.1824 * m := by
  have hm' : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
    linarith
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hrm' : 100 * (r : ℝ) ≤ m := by exact_mod_cast hrm
  have hn' : (n : ℝ) ≤ 2 * m + 1 := by exact_mod_cast hn
  have hK := log_choose_add_le m r hr
  have hB := log_choose_add_le n r hr
  have hK' := mul_log_one_add_div_le_of_le hr' hrm' (a := (m : ℝ)) (by positivity)
  have hB' := mul_log_one_add_div_le_of_le hr' hrm' (a := 2 * (m : ℝ) + 1) (by positivity)
  have hmpos : (0 : ℝ) < m := by linarith
  have h101 : 1 + 100 * (m : ℝ) / m = 101 := by field_simp; ring
  rw [h101] at hK'
  have hBn : log (1 + (n : ℝ) / r) ≤ log (1 + (2 * m + 1) / r) := by
    apply Real.log_le_log (by positivity)
    have := div_le_div_of_nonneg_right hn' hr'.le
    linarith
  have hB2 : log (1 + 100 * (2 * (m : ℝ) + 1) / m) ≤ log 201.1 := by
    apply Real.log_le_log (by positivity)
    have h1 : 100 * (2 * (m : ℝ) + 1) / m = 200 + 100 / m := by field_simp; ring
    have h2 : 100 / (m : ℝ) ≤ 0.1 := by
      rw [div_le_iff₀ hmpos]; linarith
    linarith
  have hnum : log 101 + 2 * log 201.1 < (15.23 : ℝ) := by
    have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 101 * 201.1 ^ 2)
      (by norm_num : (101 * 201.1 ^ 2 : ℝ) < 2 ^ 22 * 0.975)
    have h1 : log (101 * 201.1 ^ 2 : ℝ) = log 101 + 2 * log 201.1 := by
      rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
    have h2 : log ((2 : ℝ) ^ 22 * 0.975) = 22 * log 2 + log 0.975 := by
      rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
    have h3 : log (0.975 : ℝ) ≤ 0.975 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith [Real.log_two_lt_d9]
  have hlog : (m : ℝ) / 100 * (log 101 + 2 * log 201.1) ≤ (m : ℝ) / 100 * 15.23 :=
    mul_le_mul_of_nonneg_left hnum.le (by positivity)
  have hBn2 : (r : ℝ) * log (1 + (n : ℝ) / r) ≤ r * log (1 + (2 * m + 1) / r) :=
    mul_le_mul_of_nonneg_left hBn hr'.le
  have hB3 : (m : ℝ) / 100 * log (1 + 100 * (2 * (m : ℝ) + 1) / m) ≤ (m : ℝ) / 100 * log 201.1 :=
    mul_le_mul_of_nonneg_left hB2 (by positivity)
  nlinarith

/-! ### Theorem 1.4, explicit assertion -/

/-- **The printed numerical bounds in the proof of the explicit assertion of Theorem 1.4.**
For `m ≥ max{100r, 1000}`, with `S = 2(2m+δ)+2r+1`, `M = m+r`, `K = binom(m+r, r)` and
`B = binom(2m+δ+r, r)`:
`(log K + 2 log B)/m < 0.1824`, `(M-m) log 3/m < 0.011`, `√S log 3/m < 0.0746`,
`log(8√m)/m < 0.006`, and `0.1824 + 0.011 + 0.0746 + 0.006 = 0.274 < 2/7 < log(4/3)`. -/
theorem symmetric_range_printed_bounds (r m δ : ℕ) (hδ : δ ≤ 1) (hrm : 100 * r ≤ m)
    (hm : 1000 ≤ m) :
    log ((m + r).choose r : ℝ) + 2 * log ((2 * m + δ + r).choose r : ℝ) < 0.1824 * m ∧
    (r : ℝ) * log 3 < 0.011 * m ∧
    √((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ) * log 3 < 0.0746 * m ∧
    log (8 * √(m : ℝ)) < 0.006 * m ∧
    (0.1824 + 0.011 + 0.0746 + 0.006 : ℝ) = 0.274 ∧ (0.274 : ℝ) < 2 / 7 ∧
    (2 / 7 : ℝ) < log (4 / 3) := by
  have hm' : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hrm' : 100 * (r : ℝ) ≤ m := by exact_mod_cast hrm
  have hδ' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ
  have hl3 := log_three_lt_d4
  have hl3' : 0 < log (3 : ℝ) := Real.log_pos (by norm_num)
  have hl2 := Real.log_two_lt_d9
  refine ⟨log_choose_add_two_mul_log_choose_le r m (2 * m + δ) hrm hm (by omega), ?_, ?_, ?_,
    by norm_num, by norm_num, by linarith [log_four_div_three_gt]⟩
  · have hr : (r : ℝ) ≤ m / 100 := by linarith
    have : (r : ℝ) * log 3 ≤ m / 100 * 1.0987 := mul_le_mul hr hl3.le hl3'.le (by positivity)
    linarith
  · have hsqrt : √((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ) ≤ 0.0677 * m := by
      apply sqrt_le_of_le_sq (by positivity)
      push_cast
      nlinarith
    have := mul_le_mul hsqrt hl3.le hl3'.le (by positivity)
    nlinarith
  · have h8 := log_eight_mul_sqrt_le hmpos 10
    norm_num at h8
    linarith

/-- **The explicit assertion of Theorem 1.4.** For `r ≥ 0`, `δ ∈ {0,1}` and
`m ≥ max{100r, 1000}`, with `n = 2m+δ`, `S = 2n+2r+1`, `M = m+r`, `K = binom(m+r, r)` and
`B = binom(n+r, r)`, the elementary criterion (3.6) holds:
`m log 4 > (M + √S) log 3 + log(8√m) + log K + 2 log B - log binom(2r, r)`. -/
theorem symmetric_elementary_of_range (r m δ : ℕ) (hδ : δ ≤ 1) (hrm : 100 * r ≤ m)
    (hm : 1000 ≤ m) :
    ((m : ℝ) + r + √((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ)) * log 3 + log (8 * √(m : ℝ)) +
        log ((m + r).choose r : ℝ) + 2 * log ((2 * m + δ + r).choose r : ℝ) -
        log ((2 * r).choose r : ℝ) < m * log 4 := by
  have hm' : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hrm' : 100 * (r : ℝ) ≤ m := by exact_mod_cast hrm
  have hδ' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ
  have hKB := log_choose_add_two_mul_log_choose_le r m (2 * m + δ) hrm hm (by omega)
  have hC : 0 ≤ log ((2 * r).choose r : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.choose_pos (by omega)
  have hl3 := log_three_lt_d4
  have hl3' : 0 < log (3 : ℝ) := Real.log_pos (by norm_num)
  have hl43 := log_four_div_three_gt
  have hsqrt : √((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ) ≤ 0.068 * m := by
    apply sqrt_le_of_le_sq (by positivity)
    push_cast
    nlinarith
  have h8 := log_eight_mul_sqrt_le hmpos 10
  have hl2 := Real.log_two_lt_d9
  have hr3 : (r : ℝ) * log 3 ≤ m / 100 * 1.0987 := by
    have : (r : ℝ) ≤ m / 100 := by linarith
    exact mul_le_mul this hl3.le hl3'.le (by positivity)
  have hS3 : √((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ) * log 3 ≤ 0.068 * m * 1.0987 :=
    mul_le_mul hsqrt hl3.le hl3'.le (by positivity)
  have h43 : (0.2876 : ℝ) * m ≤ m * log (4 / 3) := by nlinarith
  rw [log_four_eq_log_three_add]
  norm_num at h8
  nlinarith

/-! ### Theorem 1.5: first derivatives (`r = 1`) -/

/-- **The case `r = 1`, `m ≥ 200`** (proof of Theorem 1.5):
`m log(4/3) > √(4m+5) log 3 + log(8√m) + log(2(m+1)²)`.

The manuscript observes that the right side divided by `m` decreases and evaluates it at `m = 200`
(`(29 · 1.1 + 5 + 12)/200 = 0.2445 < 2/7`). Here the inequality is bounded directly for every
`m ≥ 200`, without the monotonicity statement or the evaluation at `m = 200`. -/
theorem first_derivative_range (m : ℕ) (hm : 200 ≤ m) :
    √(4 * (m : ℝ) + 5) * log 3 + log (8 * √(m : ℝ)) + log (2 * ((m : ℝ) + 1) ^ 2) <
      m * log (4 / 3) := by
  have hm' : (200 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hl3 := log_three_lt_d4
  have hl3' : 0 < log (3 : ℝ) := Real.log_pos (by norm_num)
  have hl43 := log_four_div_three_gt
  have hl2 := Real.log_two_lt_d9
  have hsqrt : √(4 * (m : ℝ) + 5) ≤ 0.145 * m := by
    apply sqrt_le_of_le_sq (by positivity)
    nlinarith
  have hS3 : √(4 * (m : ℝ) + 5) * log 3 ≤ 0.145 * m * 1.0987 :=
    mul_le_mul hsqrt hl3.le hl3'.le (by positivity)
  have h8 := log_eight_mul_sqrt_le hmpos 8
  have hm1 := log_le_mul_log_two_add (by positivity : (0 : ℝ) < m + 1) 8
  have hsq : log (2 * ((m : ℝ) + 1) ^ 2) = log 2 + 2 * log ((m : ℝ) + 1) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast; ring
  have h43 : (0.2876 : ℝ) * m ≤ m * log (4 / 3) := by nlinarith
  rw [hsq]
  norm_num at h8 hm1
  nlinarith

/-- **The exact criterion (3.5) for `r = 1`, `m ≥ 200`** (conditional on [Hanson, Theorem 1]).
With `n = 2m+δ`, `S = 2n+3`, `K = binom(m+1, 1) = m+1`, and any `0 < a ≤ 2m+2` (the bound
`A_{≤m} ≤ n+1 ≤ 2m+2`): `m log 4 > Ψ_m(S) + log(8√m) + log K + log a`. -/
theorem first_derivative_exact_criterion (hH : HansonLcmBound) (m δ : ℕ) (hδ : δ ≤ 1)
    (hm : 200 ≤ m) (a : ℝ) (ha : 0 < a) (ha' : a ≤ 2 * m + 2) :
    primePowerLogSum m ((2 * (2 * m + δ) + 3 : ℕ) : ℝ) + log (8 * √(m : ℝ)) +
        log ((m + 1).choose 1 : ℝ) + log a < m * log 4 := by
  have hm' : (200 : ℝ) ≤ m := by exact_mod_cast hm
  have hδ' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ
  have hS1 : (1 : ℝ) ≤ ((2 * (2 * m + δ) + 3 : ℕ) : ℝ) := by push_cast; linarith
  have hS4 : ((2 * (2 * m + δ) + 3 : ℕ) : ℝ) ≤ 4 * m + 5 := by push_cast; linarith
  have hS5 : ((2 * (2 * m + δ) + 3 : ℕ) : ℝ) ≤ 5 * (m : ℕ) := by linarith
  obtain ⟨h1, h2⟩ := lcm_bound hH m (by omega) _ hS1 hS5
  have hsq : √((2 * (2 * m + δ) + 3 : ℕ) : ℝ) ≤ √(4 * (m : ℝ) + 5) := Real.sqrt_le_sqrt hS4
  have hl3' : 0 < log (3 : ℝ) := Real.log_pos (by norm_num)
  have hsq3 := mul_le_mul_of_nonneg_right hsq hl3'.le
  have hKa : log ((m + 1).choose 1 : ℝ) + log a ≤ log (2 * ((m : ℝ) + 1) ^ 2) := by
    rw [Nat.choose_one_right]
    push_cast
    rw [← Real.log_mul (by positivity) ha.ne']
    apply Real.log_le_log (by positivity)
    nlinarith
  have hmain := first_derivative_range m hm
  rw [log_four_eq_log_three_add]
  nlinarith

/-! ### Theorem 1.5: Legendre polynomials (`r = 0`) -/

/-- **The case `r = 0`, `m ≥ 100`** (proof of Theorem 1.5):
`m log(4/3) > √(4m+3) log 3 + log(8√m)`.

The manuscript observes that the right side divided by `m` decreases and evaluates it at `m = 100`
(less than `0.275 < 2/7 < log(4/3)`). Here the inequality is bounded directly for every
`m ≥ 100`, without the monotonicity statement or the evaluation at `m = 100`. -/
theorem legendre_range (m : ℕ) (hm : 100 ≤ m) :
    √(4 * (m : ℝ) + 3) * log 3 + log (8 * √(m : ℝ)) < m * log (4 / 3) := by
  have hm' : (100 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hl3 := log_three_lt_d4
  have hl3' : 0 < log (3 : ℝ) := Real.log_pos (by norm_num)
  have hl43 := log_four_div_three_gt
  have hl2 := Real.log_two_lt_d9
  have hsqrt : √(4 * (m : ℝ) + 3) ≤ 0.205 * m := by
    apply sqrt_le_of_le_sq (by positivity)
    nlinarith
  have hS3 : √(4 * (m : ℝ) + 3) * log 3 ≤ 0.205 * m * 1.0987 :=
    mul_le_mul hsqrt hl3.le hl3'.le (by positivity)
  have h8 := log_eight_mul_sqrt_le hmpos 7
  have h43 : (0.2876 : ℝ) * m ≤ m * log (4 / 3) := by nlinarith
  norm_num at h8
  nlinarith

/-- **The exact criterion (3.5) for `r = 0`, `m ≥ 100`** (conditional on [Hanson, Theorem 1]).
Here `K = A = 1`, so `log K = log A_{≤m} = 0`; with `n = 2m+δ` and `S = 2n+1`:
`m log 4 > Ψ_m(S) + log(8√m)`. -/
theorem legendre_exact_criterion (hH : HansonLcmBound) (m δ : ℕ) (hδ : δ ≤ 1) (hm : 100 ≤ m) :
    primePowerLogSum m ((2 * (2 * m + δ) + 1 : ℕ) : ℝ) + log (8 * √(m : ℝ)) < m * log 4 := by
  have hm' : (100 : ℝ) ≤ m := by exact_mod_cast hm
  have hδ' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ
  have hS1 : (1 : ℝ) ≤ ((2 * (2 * m + δ) + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hS4 : ((2 * (2 * m + δ) + 1 : ℕ) : ℝ) ≤ 4 * m + 3 := by push_cast; linarith
  have hS5 : ((2 * (2 * m + δ) + 1 : ℕ) : ℝ) ≤ 5 * (m : ℕ) := by linarith
  obtain ⟨h1, h2⟩ := lcm_bound hH m (by omega) _ hS1 hS5
  have hsq : √((2 * (2 * m + δ) + 1 : ℕ) : ℝ) ≤ √(4 * (m : ℝ) + 3) := Real.sqrt_le_sqrt hS4
  have hl3' : 0 < log (3 : ℝ) := Real.log_pos (by norm_num)
  have hsq3 := mul_le_mul_of_nonneg_right hsq hl3'.le
  have hmain := legendre_range m hm
  rw [log_four_eq_log_three_add]
  nlinarith

end ArithmeticOfJacobiPolynomials
