/- Assembled by AxiomProver. -/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Numerical margins

The rational verification of the positive gap (4.20) and the logarithmic margins of
Appendix C.3, together with the function `g` of (3.18).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Real Finset

/-- The function `g(t) = (4t+2) log(t+1/2) - 3t log t - (t+1) log(t+1)` of (3.18). -/
noncomputable def symmetricGapFunction (t : ℝ) : ℝ :=
  (4 * t + 2) * log (t + 1 / 2) - 3 * t * log t - (t + 1) * log (t + 1)

/-- Lower bound of `log((1+z)/(1-z))` by partial sums of the inverse hyperbolic tangent series. -/
theorem two_mul_sum_le_log_div {z : ℝ} (h₀ : 0 ≤ z) (h₁ : z < 1) (n : ℕ) :
    2 * ∑ i ∈ range n, z ^ (2 * i + 1) / (2 * i + 1) ≤ log ((1 + z) / (1 - z)) := by
  linarith [Real.sum_range_le_log_div h₀ h₁ n]

/-- Upper bound of `log((1+z)/(1-z))` by partial sums plus a geometric tail. -/
theorem log_div_le_two_mul_sum_add {z : ℝ} (h₀ : 0 ≤ z) (h₁ : z < 1) (n : ℕ) :
    log ((1 + z) / (1 - z)) ≤
      2 * ((∑ i ∈ range n, z ^ (2 * i + 1) / (2 * i + 1)) + z ^ (2 * n + 1) / (1 - z ^ 2)) := by
  linarith [Real.log_div_le_sum_range_add h₀ h₁ n]

/-! ### The sharp series tail of Appendix B.2 / C.3

The remainder `ℰ_r(t) = log((1+t)/(1-t)) - 2 ∑_{j<r} t^(2j+1)/(2j+1)` satisfies
`0 ≤ ℰ_r(t) ≤ 2 t^(2r+1)/((2r+1)(1-t²))` (Appendix B.2, displayed for `0 ≤ t ≤ 1/3`; here for all
`0 ≤ t < 1`), strictly on both sides for `0 < t < 1`. The proof uses the derivative formula
`F'(x) = (x²)^r/(1-x²)` of `F(x) = ½ log((1+x)/(1-x)) - ∑_{j<r} x^(2j+1)/(2j+1)`
(`Real.hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range`) and the auxiliary function
`G(x) = x^(2r+1)/((2r+1)(1-x²)) - F(x)`, whose derivative is `2x^(2r+2)/((2r+1)(1-x²)²) > 0`. -/

/-- `F(x) = ½ log((1+x)/(1-x)) - ∑_{j<r} x^(2j+1)/(2j+1)`. -/
noncomputable def logSeriesRemainder (r : ℕ) (x : ℝ) : ℝ :=
  1 / 2 * log ((1 + x) / (1 - x)) - ∑ i ∈ range r, x ^ (2 * i + 1) / (2 * i + 1)

theorem hasDerivAt_logSeriesRemainder (r : ℕ) {y : ℝ} (h₁ : -1 < y) (h₂ : y < 1) :
    HasDerivAt (logSeriesRemainder r) ((y ^ 2) ^ r / (1 - y ^ 2)) y :=
  Real.hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range r h₁ h₂

theorem logSeriesRemainder_zero (r : ℕ) : logSeriesRemainder r 0 = 0 := by
  cases r <;> simp [logSeriesRemainder]

/-- The auxiliary function `G(x) = x^(2r+1)/((2r+1)(1-x²)) - F(x)`. -/
noncomputable def logSeriesGap (r : ℕ) (x : ℝ) : ℝ :=
  x ^ (2 * r + 1) / ((2 * r + 1) * (1 - x ^ 2)) - logSeriesRemainder r x

theorem hasDerivAt_logSeriesGap (r : ℕ) {y : ℝ} (h₁ : -1 < y) (h₂ : y < 1) :
    HasDerivAt (logSeriesGap r) (2 * y ^ (2 * r + 2) / ((2 * r + 1) * (1 - y ^ 2) ^ 2)) y := by
  have hy : 1 - y ^ 2 ≠ 0 := by nlinarith
  have hr : (2 * (r : ℝ) + 1) ≠ 0 := by positivity
  have hnum : HasDerivAt (fun x : ℝ => x ^ (2 * r + 1)) ((2 * r + 1) * y ^ (2 * r)) y := by
    simpa using hasDerivAt_pow (2 * r + 1) y
  have hden : HasDerivAt (fun x : ℝ => (2 * (r : ℝ) + 1) * (1 - x ^ 2))
      ((2 * (r : ℝ) + 1) * (-(2 * y))) y := by
    have := ((hasDerivAt_pow 2 y).const_sub 1).const_mul (2 * (r : ℝ) + 1)
    simpa using this
  have hq := hnum.div hden (mul_ne_zero hr hy)
  have hG := hq.sub (hasDerivAt_logSeriesRemainder r h₁ h₂)
  refine (hG.congr_deriv ?_)
  have e : (y ^ 2) ^ r = y ^ (2 * r) := by rw [← pow_mul]
  rw [e]
  have e2 : y ^ (2 * r + 2) = y ^ (2 * r) * y ^ 2 := by ring
  rw [e2, show y ^ (2 * r + 1) = y ^ (2 * r) * y by ring]
  field_simp
  ring

theorem logSeriesRemainder_pos {x : ℝ} (r : ℕ) (h₀ : 0 < x) (h₁ : x < 1) :
    0 < logSeriesRemainder r x := by
  have hmono : StrictMonoOn (logSeriesRemainder r) (Set.Icc 0 x) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 x) ?_ ?_
    · intro y hy
      exact (hasDerivAt_logSeriesRemainder r (by linarith [hy.1])
        (by linarith [hy.2])).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      rw [(hasDerivAt_logSeriesRemainder r (by linarith [hy.1]) (by linarith [hy.2])).deriv]
      have : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
      have : 0 < y ^ 2 := by nlinarith [hy.1]
      positivity
  have := hmono ⟨le_rfl, h₀.le⟩ ⟨h₀.le, le_rfl⟩ h₀
  rwa [logSeriesRemainder_zero] at this

theorem logSeriesGap_pos {x : ℝ} (r : ℕ) (h₀ : 0 < x) (h₁ : x < 1) : 0 < logSeriesGap r x := by
  have hmono : StrictMonoOn (logSeriesGap r) (Set.Icc 0 x) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 x) ?_ ?_
    · intro y hy
      exact (hasDerivAt_logSeriesGap r (by linarith [hy.1])
        (by linarith [hy.2])).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      rw [(hasDerivAt_logSeriesGap r (by linarith [hy.1]) (by linarith [hy.2])).deriv]
      have : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
      have : 0 < y := hy.1
      positivity
  have h0 : logSeriesGap r 0 = 0 := by
    simp [logSeriesGap, logSeriesRemainder_zero]
  have := hmono ⟨le_rfl, h₀.le⟩ ⟨h₀.le, le_rfl⟩ h₀
  rwa [h0] at this

/-- Strict lower bound: `2 ∑_{j<r} z^(2j+1)/(2j+1) < log((1+z)/(1-z))` for `0 < z < 1`. -/
theorem two_mul_sum_lt_log_div {z : ℝ} (h₀ : 0 < z) (h₁ : z < 1) (r : ℕ) :
    2 * ∑ i ∈ range r, z ^ (2 * i + 1) / (2 * i + 1) < log ((1 + z) / (1 - z)) := by
  have := logSeriesRemainder_pos r h₀ h₁
  unfold logSeriesRemainder at this
  linarith

/-- **Sharp strict upper bound**: `log((1+z)/(1-z)) < 2 ∑_{j<r} z^(2j+1)/(2j+1) +
2 z^(2r+1)/((2r+1)(1-z²))` for `0 < z < 1`. -/
theorem log_div_lt_two_mul_sum_add_sharp {z : ℝ} (h₀ : 0 < z) (h₁ : z < 1) (r : ℕ) :
    log ((1 + z) / (1 - z)) < 2 * ∑ i ∈ range r, z ^ (2 * i + 1) / (2 * i + 1) +
      2 * z ^ (2 * r + 1) / ((2 * r + 1) * (1 - z ^ 2)) := by
  have h := logSeriesGap_pos r h₀ h₁
  unfold logSeriesGap logSeriesRemainder at h
  have e : 2 * z ^ (2 * r + 1) / ((2 * (r : ℝ) + 1) * (1 - z ^ 2)) =
      2 * (z ^ (2 * r + 1) / ((2 * (r : ℝ) + 1) * (1 - z ^ 2))) := by ring
  rw [e]
  linarith

/-- The truncation bounds of Appendix B.2 (`ℰ_r(t) = log((1+t)/(1-t)) - 2 ∑_{j<r} t^(2j+1)/(2j+1)`):
`0 ≤ ℰ_r(t) ≤ 2 t^(2r+1)/((2r+1)(1-t²))` for `0 ≤ t < 1` (in particular for `0 ≤ t ≤ 1/3`). -/
theorem log_series_remainder_bounds {t : ℝ} (h₀ : 0 ≤ t) (h₁ : t < 1) (r : ℕ) :
    0 ≤ log ((1 + t) / (1 - t)) - 2 * ∑ i ∈ range r, t ^ (2 * i + 1) / (2 * i + 1) ∧
      log ((1 + t) / (1 - t)) - 2 * ∑ i ∈ range r, t ^ (2 * i + 1) / (2 * i + 1) ≤
        2 * t ^ (2 * r + 1) / ((2 * r + 1) * (1 - t ^ 2)) := by
  rcases h₀.eq_or_lt with rfl | h
  · cases r <;> simp
  · have h1 := two_mul_sum_lt_log_div h h₁ r
    have h2 := log_div_lt_two_mul_sum_add_sharp h h₁ r
    constructor <;> linarith

/-- `T(z) = 2 ∑_{j=0}^{4} z^(2j+1)/(2j+1)` (Appendix C.3). -/
noncomputable def logSeriesT (z : ℝ) : ℝ := 2 * ∑ j ∈ range 5, z ^ (2 * j + 1) / (2 * j + 1)

/-- `U_*(z) = T(z) + 2 z^11 / (11 (1 - z²))` (Appendix C.3). -/
noncomputable def logSeriesUStar (z : ℝ) : ℝ := logSeriesT z + 2 * z ^ 11 / (11 * (1 - z ^ 2))

/-- Appendix C.3: `T(z) < log((1+z)/(1-z))` for `0 < z < 1`. -/
theorem logSeriesT_lt_log_div {z : ℝ} (h₀ : 0 < z) (h₁ : z < 1) :
    logSeriesT z < log ((1 + z) / (1 - z)) :=
  two_mul_sum_lt_log_div h₀ h₁ 5

/-- Appendix C.3: `log((1+z)/(1-z)) < U_*(z)` for `0 < z < 1`. -/
theorem log_div_lt_logSeriesUStar {z : ℝ} (h₀ : 0 < z) (h₁ : z < 1) :
    log ((1 + z) / (1 - z)) < logSeriesUStar z := by
  have := log_div_lt_two_mul_sum_add_sharp h₀ h₁ 5
  unfold logSeriesUStar logSeriesT
  norm_num at this ⊢
  linarith

/-- The `T`-bound for the logarithm of an explicit rational `q = (1+z)/(1-z)`. -/
theorem logSeriesT_lt_log {z q : ℝ} (h₀ : 0 < z) (h₁ : z < 1) (hq : q = (1 + z) / (1 - z)) :
    logSeriesT z < log q := hq ▸ logSeriesT_lt_log_div h₀ h₁

theorem log_lt_logSeriesUStar {z q : ℝ} (h₀ : 0 < z) (h₁ : z < 1) (hq : q = (1 + z) / (1 - z)) :
    log q < logSeriesUStar z := hq ▸ log_div_lt_logSeriesUStar h₀ h₁

/-- First rational comparison of Appendix C.3:
`13 T(1/3) + 9 T(1/17) - 34 U_*(1/33) - 8 > 97/10000`. -/
theorem rational_margin_eight :
    13 * logSeriesT (1 / 3) + 9 * logSeriesT (1 / 17) - 34 * logSeriesUStar (1 / 33) - 8 >
      97 / 10000 := by
  norm_num [logSeriesT, logSeriesUStar, Finset.sum_range_succ]

/-- Second rational comparison of Appendix C.3:
`3 T(1/3) + 8 T(1/5) + 57 T(3/35) + 92 T(1/47) - 19 > 42/1250 = 8 · 21/5000`. -/
theorem rational_margin_nineteen_eighths :
    3 * logSeriesT (1 / 3) + 8 * logSeriesT (1 / 5) + 57 * logSeriesT (3 / 35) +
      92 * logSeriesT (1 / 47) - 19 > 42 / 1250 := by
  norm_num [logSeriesT, Finset.sum_range_succ]

theorem log_nine_div_eight_gt : (0.1177830356 : ℝ) < log (9 / 8) := by
  have h := two_mul_sum_le_log_div (z := 1 / 17) (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem log_seventeen_div_sixteen_lt : log (17 / 16) < (0.0606246219 : ℝ) := by
  have h := log_div_le_two_mul_sum_add (z := 1 / 33) (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem log_three_div_two_gt : (0.4054650 : ℝ) < log (3 / 2) := by
  have h := two_mul_sum_le_log_div (z := 1 / 5) (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem log_nineteen_div_sixteen_gt : (0.1718502569 : ℝ) < log (19 / 16) := by
  have h := two_mul_sum_le_log_div (z := 3 / 35) (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem log_twentyfour_div_twentythree_gt : (0.0425596144 : ℝ) < log (24 / 23) := by
  have h := two_mul_sum_le_log_div (z := 1 / 47) (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem log_three_gt : (549 / 500 : ℝ) < log 3 := by
  have h : log (3 / 2) = log 3 - log 2 := Real.log_div (by norm_num) (by norm_num)
  linarith [log_three_div_two_gt, Real.log_two_gt_d9]

/-- The positive gap (4.20): `𝔩 - 𝔲 > 1/4`. -/
theorem positive_gap :
    log (4 + 3 * √3) - 1 / 2 * log 2 - 1 / 3 * log 3 - 43 / 20 + π / (2 * √3) > 1 / 4 := by
  have hs₁ : (1.732 : ℝ) < √3 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hs₂ : √3 < (1.733 : ℝ) := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hpos : 0 < 4 + 3 * √3 := by positivity
  have hsplit : log ((4 + 3 * √3) / 9) = log (4 + 3 * √3) - log 9 :=
    Real.log_div hpos.ne' (by norm_num)
  have h9 : log 9 = 2 * log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlow := Real.one_sub_inv_le_log_of_pos (x := (4 + 3 * √3) / 9) (by positivity)
  have hinv : ((4 + 3 * √3) / 9)⁻¹ ≤ 2250 / 2299 := by
    rw [inv_div, div_le_div_iff₀ hpos (by norm_num)]
    nlinarith
  have hpi : (1570 / 1733 : ℝ) < π / (2 * √3) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_d2]
  linarith [log_three_gt, Real.log_two_lt_d9]

theorem log_nat_div_pow_two (a k : ℕ) (ha : a ≠ 0) :
    log ((a : ℝ) / 2 ^ k) = log a - k * log 2 := by
  rw [Real.log_div (by exact_mod_cast ha) (by positivity), Real.log_pow]

/-- First margin of Appendix C.3: `8(log 4 - 1) - g(8) > 97/10000`. -/
theorem margin_at_eight :
    8 * (log 4 - 1) - symmetricGapFunction 8 > 97 / 10000 := by
  have hg : symmetricGapFunction 8 = 34 * log (17 / 2) - 24 * log 8 - 9 * log 9 := by
    unfold symmetricGapFunction; norm_num
  have h4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h8 : log 8 = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have h9 : log 9 = 2 * log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h172 : log (17 / 2) = log 17 - log 2 := Real.log_div (by norm_num) (by norm_num)
  have h98 : log (9 / 8) = log 9 - log 8 := Real.log_div (by norm_num) (by norm_num)
  have h1716 : log (17 / 16) = log 17 - 4 * log 2 := by
    have := log_nat_div_pow_two 17 4 (by norm_num); norm_num at this; exact this
  linarith [log_nine_div_eight_gt, log_seventeen_div_sixteen_lt, Real.log_two_gt_d9]

/-- Second margin of Appendix C.3: `(19/8)(log 6 - 1) - g(19/8) > 0.0042`. -/
theorem margin_at_nineteen_eighths :
    19 / 8 * (log 6 - 1) - symmetricGapFunction (19 / 8) > 0.0042 := by
  have hg : symmetricGapFunction (19 / 8) =
      23 / 2 * log (23 / 8) - 57 / 8 * log (19 / 8) - 27 / 8 * log (27 / 8) := by
    unfold symmetricGapFunction; norm_num
  have h6 : log 6 = log 2 + log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h27 : log 27 = 3 * log 3 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]; norm_num
  have h238 : log (23 / 8) = log 23 - 3 * log 2 := by
    have := log_nat_div_pow_two 23 3 (by norm_num); norm_num at this; exact this
  have h198 : log (19 / 8) = log 19 - 3 * log 2 := by
    have := log_nat_div_pow_two 19 3 (by norm_num); norm_num at this; exact this
  have h278 : log (27 / 8) = log 27 - 3 * log 2 := by
    have := log_nat_div_pow_two 27 3 (by norm_num); norm_num at this; exact this
  have h1916 : log (19 / 16) = log 19 - 4 * log 2 := by
    have := log_nat_div_pow_two 19 4 (by norm_num); norm_num at this; exact this
  have h32 : log (3 / 2) = log 3 - log 2 := Real.log_div (by norm_num) (by norm_num)
  have h2423 : log (24 / 23) = log 24 - log 23 := Real.log_div (by norm_num) (by norm_num)
  have h24 : log 24 = 3 * log 2 + log 3 := by
    rw [show (24 : ℝ) = 2 ^ 3 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]; norm_num
  linarith [log_three_div_two_gt, log_nineteen_div_sixteen_gt,
    log_twentyfour_div_twentythree_gt, Real.log_two_gt_d9]

/-- Exact form of the third margin of Appendix C.3:
`2(log 9 - 1) - g(2) = log(3^7 2^16 / 5^10) - 2`. -/
theorem margin_at_two_eq :
    2 * (log 9 - 1) - symmetricGapFunction 2 = log (3 ^ 7 * 2 ^ 16 / 5 ^ 10) - 2 := by
  have hg : symmetricGapFunction 2 = 10 * log (5 / 2) - 6 * log 2 - 3 * log 3 := by
    unfold symmetricGapFunction; norm_num
  have h52 : log (5 / 2) = log 5 - log 2 := Real.log_div (by norm_num) (by norm_num)
  have hbig : log ((3 : ℝ) ^ 7 * 2 ^ 16 / 5 ^ 10) = 7 * log 3 + 16 * log 2 - 10 * log 5 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast; ring
  have h9 : log 9 = 2 * log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [hg, h52, hbig, h9]
  ring

/-- Third margin of Appendix C.3: `2(log 9 - 1) - g(2) > 0`. -/
theorem margin_at_two : 2 * (log 9 - 1) - symmetricGapFunction 2 > 0 := by
  rw [margin_at_two_eq]
  have h2 : (2 : ℝ) < log 9 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have h := Real.exp_one_lt_d9
    have h0 := Real.exp_pos 1
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  have hmono : log 9 < log (3 ^ 7 * 2 ^ 16 / 5 ^ 10) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  linarith

/-- The exact expression of the first margin in Appendix C.3:
`8(log 4 - 1) - g(8) = 13 log 2 + 9 log(9/8) - 34 log(17/16) - 8`. -/
theorem margin_at_eight_exact_expression :
    8 * (log 4 - 1) - symmetricGapFunction 8 =
      13 * log 2 + 9 * log (9 / 8) - 34 * log (17 / 16) - 8 := by
  have hg : symmetricGapFunction 8 = 34 * log (17 / 2) - 24 * log 8 - 9 * log 9 := by
    unfold symmetricGapFunction; norm_num
  have h4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h8 : log 8 = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have h9 : log 9 = 2 * log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h172 : log (17 / 2) = log 17 - log 2 := Real.log_div (by norm_num) (by norm_num)
  have h98 : log (9 / 8) = log 9 - log 8 := Real.log_div (by norm_num) (by norm_num)
  have h1716 : log (17 / 16) = log 17 - 4 * log 2 := by
    have := log_nat_div_pow_two 17 4 (by norm_num); norm_num at this; exact this
  rw [hg, h172, h98, h1716, h4, h8, h9]
  ring

/-- The exact expression of the second margin in Appendix C.3:
`8 [(19/8)(log 6 - 1) - g(19/8)] = 3 log 2 + 8 log(3/2) + 57 log(19/16) + 92 log(24/23) - 19`. -/
theorem margin_at_nineteen_eighths_exact_expression :
    8 * (19 / 8 * (log 6 - 1) - symmetricGapFunction (19 / 8)) =
      3 * log 2 + 8 * log (3 / 2) + 57 * log (19 / 16) + 92 * log (24 / 23) - 19 := by
  have hg : symmetricGapFunction (19 / 8) =
      23 / 2 * log (23 / 8) - 57 / 8 * log (19 / 8) - 27 / 8 * log (27 / 8) := by
    unfold symmetricGapFunction; norm_num
  have h6 : log 6 = log 2 + log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h27 : log 27 = 3 * log 3 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]; norm_num
  have h238 : log (23 / 8) = log 23 - 3 * log 2 := by
    have := log_nat_div_pow_two 23 3 (by norm_num); norm_num at this; exact this
  have h198 : log (19 / 8) = log 19 - 3 * log 2 := by
    have := log_nat_div_pow_two 19 3 (by norm_num); norm_num at this; exact this
  have h278 : log (27 / 8) = log 27 - 3 * log 2 := by
    have := log_nat_div_pow_two 27 3 (by norm_num); norm_num at this; exact this
  have h1916 : log (19 / 16) = log 19 - 4 * log 2 := by
    have := log_nat_div_pow_two 19 4 (by norm_num); norm_num at this; exact this
  have h32 : log (3 / 2) = log 3 - log 2 := Real.log_div (by norm_num) (by norm_num)
  have h2423 : log (24 / 23) = log 24 - log 23 := Real.log_div (by norm_num) (by norm_num)
  have h24 : log 24 = 3 * log 2 + log 3 := by
    rw [show (24 : ℝ) = 2 ^ 3 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]; norm_num
  rw [hg, h238, h198, h278, h6, h27, h32, h1916, h2423, h24]
  ring

/-- For the first margin of Appendix C.3, the manuscript uses the exact expression, the strict
bounds `T(z) < log((1+z)/(1-z)) < U_*(z)` and the rational comparison `rational_margin_eight`. -/
theorem margin_at_eight_of_rational :
    8 * (log 4 - 1) - symmetricGapFunction 8 > 97 / 10000 := by
  have h2 := logSeriesT_lt_log (z := 1 / 3) (q := 2) (by norm_num) (by norm_num) (by norm_num)
  have h98 := logSeriesT_lt_log (z := 1 / 17) (q := 9 / 8) (by norm_num) (by norm_num)
    (by norm_num)
  have h1716 := log_lt_logSeriesUStar (z := 1 / 33) (q := 17 / 16) (by norm_num) (by norm_num)
    (by norm_num)
  have hr := rational_margin_eight
  rw [margin_at_eight_exact_expression]
  linarith

/-- Second margin of Appendix C.3 (`42/1250 = 8 · 21/5000`). -/
theorem margin_at_nineteen_eighths_of_rational :
    19 / 8 * (log 6 - 1) - symmetricGapFunction (19 / 8) > 21 / 5000 := by
  have h2 := logSeriesT_lt_log (z := 1 / 3) (q := 2) (by norm_num) (by norm_num) (by norm_num)
  have h32 := logSeriesT_lt_log (z := 1 / 5) (q := 3 / 2) (by norm_num) (by norm_num)
    (by norm_num)
  have h1916 := logSeriesT_lt_log (z := 3 / 35) (q := 19 / 16) (by norm_num) (by norm_num)
    (by norm_num)
  have h2423 := logSeriesT_lt_log (z := 1 / 47) (q := 24 / 23) (by norm_num) (by norm_num)
    (by norm_num)
  have hr := rational_margin_nineteen_eighths
  have hx := margin_at_nineteen_eighths_exact_expression
  linarith

end ArithmeticOfJacobiPolynomials
