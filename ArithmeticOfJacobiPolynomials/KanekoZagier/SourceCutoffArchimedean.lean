/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.ExplicitCutoff
public import ArithmeticOfJacobiPolynomials.KanekoZagier.ExplicitCutoffLower

/-!
# Proposition B.1: the archimedean estimates exactly as printed

This file proves the intermediate estimates of "The necessary archimedean inequality" in the
proof of Proposition B.1 with the printed constants, rather than the digit-sum error of
`kz_lambda_ge_sub` or the cruder error `6 log(3n + 1) + 10` of `kz_lambda_ge_log`:

* `kz_nL_ge`: `n L_n ≥ n L_* - log(6n+3)`;
* `kz_logKappa_sub_ge`: `log κ_n - n (T_{2,n} + T_{3,n}) ≥ -log(3n+1) - 2 log(3n) - (1/2) log 3`;
* `kzJ_le`: `J_n ≤ (1/2) log(2n) + (1/3) log(6n+3)`;
* `kz_brace_le`: the braces are at most `6 log(12n)`;
* `kz_arch_source`: `S_n + log g_n`'s lower bound `n(L_* - E) - 6 log(12n)`, in the form of the
  quantity bounded below in `kz_lower_bound_of_not_irreducible`;
* `abs_kzT2_sub_kzT3_lt`: `|T_{2,n} - T_{3,n}| < 3/10` for `n ≥ 250000`;
* `kzLStar_sub_kzE_gt_three_halves`: `L_* - E > 3/2` by the printed rational estimate
  `34478/22975`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Finset

/-! ### Elementary numerics -/

theorem exp_fifteen_gt : (3000000 : ℝ) < Real.exp 15 := by
  have h15 : Real.exp 1 ^ 15 = Real.exp 15 := by rw [Real.exp_one_pow]; norm_num
  rw [← h15]
  calc (3000000 : ℝ) < (2.7182818283 : ℝ) ^ 15 := by norm_num
    _ < Real.exp 1 ^ 15 :=
        pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)

/-- `log x ≤ log y + x/y - 1`. -/
theorem kz_log_le_log_add_div_sub_one {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log x ≤ Real.log y + x / y - 1 := by
  have := Real.log_le_sub_one_of_pos (show 0 < x / y by positivity)
  rw [Real.log_div hx.ne' hy.ne'] at this
  linarith

/-- `log(c n)/n` decreases for `n ≥ N` once `log(c N) ≥ 1`. -/
theorem log_mul_div_le_of_le {c n N : ℝ} (hc : 0 < c) (hN : 0 < N) (hn : N ≤ n)
    (h1 : 1 ≤ Real.log (c * N)) : Real.log (c * n) / n ≤ Real.log (c * N) / N := by
  have hn0 : 0 < n := lt_of_lt_of_le hN hn
  have h := kz_log_le_log_add_div_sub_one (x := c * n) (y := c * N) (by positivity) (by positivity)
  rw [mul_div_mul_left _ _ hc.ne'] at h
  rw [div_le_div_iff₀ hn0 hN]
  have h2 : Real.log (c * n) * N ≤ (Real.log (c * N) + n / N - 1) * N :=
    mul_le_mul_of_nonneg_right h hN.le
  have h3 : n / N * N = n := div_mul_cancel₀ _ hN.ne'
  nlinarith [mul_nonneg (sub_nonneg.mpr hn) (sub_nonneg.mpr h1)]

/-! ### The three printed estimates -/

/-- `n L_n ≥ n L_* - log(6n+3)`. -/
theorem kz_nL_ge {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) {n : ℕ} (hn : 1 ≤ n) :
    n * Real.log (4 + 3 * √3) - Real.log (6 * n + 3) ≤ n * kzL l μ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨-, h2, -, h4, -, -, -, hδ, hδ0⟩ := kz_log_facts hμ hn
  obtain ⟨hD2lo, -⟩ := kzEndpointTwo_bounds hl n
  have hD3 := two_mul_kzEndpointThree hμ n
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set u := Real.log (6 * n + 3) with hu
  have hlogn : Real.log n + Real.log 2 = Real.log (2 * n) := by
    rw [Real.log_mul (by norm_num) hn0.ne']; ring
  have hs2 : ((Nat.digits 2 n).sum : ℝ) * Real.log 2 ≤ u := by
    have : Real.log (2 * n) ≤ u := Real.log_le_log (by positivity) (by linarith)
    linarith
  have hs3 : ((Nat.digits 3 (2 * n + kzDelta μ)).sum : ℝ) * Real.log 3 / 2 ≤ u := by
    have e : Real.log (2 * n + kzDelta μ) + Real.log 3 = Real.log (3 * (2 * n + kzDelta μ)) := by
      rw [Real.log_mul (by norm_num) (by positivity)]; ring
    have : Real.log (3 * (2 * n + kzDelta μ)) ≤ u :=
      Real.log_le_log (by positivity) (by nlinarith)
    linarith
  have hT2 : 2 * Real.log 2 - u / n ≤ kzT2 l n := by
    rw [kzT2_eq, le_div_iff₀ hn0, sub_mul, div_mul_cancel₀ _ hn0.ne']
    have := mul_le_mul_of_nonneg_right hD2lo hl2.le
    nlinarith
  have hT3 : 3 / 2 * Real.log 3 - u / n ≤ kzT3 μ n := by
    rw [kzT3_eq, le_div_iff₀ hn0, sub_mul, div_mul_cancel₀ _ hn0.ne']
    have hs3n : (0 : ℝ) ≤ (Nat.digits 3 n).sum := Nat.cast_nonneg _
    have p1 := mul_nonneg hs3n hl3.le
    have p2 := mul_nonneg hδ0 hl3.le
    have hD3l : 2 * (kzEndpointThree μ n : ℝ) * Real.log 3 =
        (3 * n + kzDelta μ + (Nat.digits 3 n).sum - (Nat.digits 3 (2 * n + kzDelta μ)).sum) *
          Real.log 3 := by rw [hD3]
    nlinarith
  have hL := kzL_ge hT2 hT3
  have := mul_le_mul_of_nonneg_left hL hn0.le
  have e : (n : ℝ) * (u / n) = u := mul_div_cancel₀ _ hn0.ne'
  nlinarith

/-- `log κ_n - n (T_{2,n} + T_{3,n}) ≥ -log(3n+1) - 2 log(3n) - (1/2) log 3`. -/
theorem kz_logKappa_sub_ge {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) {n : ℕ}
    (hn : 1 ≤ n) :
    -Real.log (3 * n + 1) - 2 * Real.log (3 * n) - Real.log 3 / 2 ≤
      Real.log (kzKappa n) - n * (kzT2 l n + kzT3 μ n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨h1, -, h3, -, -, -, -, hδ, hδ0⟩ := kz_log_facts hμ hn
  obtain ⟨-, hD2hi⟩ := kzEndpointTwo_bounds hl n
  have hD3 := two_mul_kzEndpointThree hμ n
  have hκ := log_kzKappa_eq n
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hT2 : (n : ℝ) * kzT2 l n = kzEndpointTwo l n * Real.log 2 := by
    rw [kzT2_eq, mul_div_assoc', mul_div_cancel_left₀ _ hn0.ne']
  have hT3 : (n : ℝ) * kzT3 μ n = kzEndpointThree μ n * Real.log 3 := by
    rw [kzT3_eq, mul_div_assoc', mul_div_cancel_left₀ _ hn0.ne']
  have hs3' : (0 : ℝ) ≤ (Nat.digits 3 (2 * n + kzDelta μ)).sum := Nat.cast_nonneg _
  have p3 := mul_nonneg hs3' hl3.le
  have p5 := mul_le_mul_of_nonneg_right hδ hl3.le
  have hD2b := mul_le_mul_of_nonneg_right hD2hi hl2.le
  have hD3l : 2 * (kzEndpointThree μ n : ℝ) * Real.log 3 =
      (3 * n + kzDelta μ + (Nat.digits 3 n).sum - (Nat.digits 3 (2 * n + kzDelta μ)).sum) *
        Real.log 3 := by rw [hD3]
  have e3n : Real.log (3 * n) = Real.log 3 + Real.log n := by
    rw [Real.log_mul (by norm_num) hn0.ne']
  rw [mul_add, hT2, hT3, hκ, e3n]
  nlinarith

/-- `J_n ≤ (1/2) log(2n) + (1/3) log(6n+3)`. -/
theorem kzJ_le {μ : ℤ} (hμ : μ = 1 ∨ μ = -1) {n : ℕ} (hn : 1 ≤ n) :
    kzJ μ n ≤ Real.log (2 * n) / 2 + Real.log (6 * n + 3) / 3 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨-, h2, -, h4, -, -, -, hδ, hδ0⟩ := kz_log_facts hμ hn
  have e2 : Real.log n + Real.log 2 = Real.log (2 * n) := by
    rw [Real.log_mul (by norm_num) hn0.ne']; ring
  have e3 : Real.log (2 * n + kzDelta μ) + Real.log 3 = Real.log (3 * (2 * n + kzDelta μ)) := by
    rw [Real.log_mul (by norm_num) (by positivity)]; ring
  have h5 : Real.log (3 * (2 * n + kzDelta μ)) ≤ Real.log (6 * n + 3) :=
    Real.log_le_log (by positivity) (by nlinarith)
  rw [kzJ_eq]
  linarith

/-- The braces of the manuscript are at most `6 log(12n)`. -/
theorem kz_brace_le {n : ℕ} (hn : 1 ≤ n) :
    4 / 3 * Real.log (6 * n + 3) + Real.log (3 * n + 1) + 2 * Real.log (3 * n) +
        Real.log (2 * n) / 2 + Real.log 3 / 2 + 4 * Real.log 2 ≤ 6 * Real.log (12 * n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hln : 0 ≤ Real.log n := Real.log_nonneg hn1
  have a1 : Real.log (6 * n + 3) ≤ Real.log 9 + Real.log n := by
    rw [← Real.log_mul (by norm_num) hn0.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  have a2 : Real.log (3 * n + 1) ≤ Real.log 4 + Real.log n := by
    rw [← Real.log_mul (by norm_num) hn0.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  have a3 : Real.log (3 * n) = Real.log 3 + Real.log n := Real.log_mul (by norm_num) hn0.ne'
  have a4 : Real.log (2 * n) = Real.log 2 + Real.log n := Real.log_mul (by norm_num) hn0.ne'
  have a5 : Real.log (12 * n) = Real.log 12 + Real.log n := Real.log_mul (by norm_num) hn0.ne'
  have b9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have b4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have b12 : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
    rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]; norm_num
  rw [a3, a4, a5, b12]
  rw [b9] at a1
  rw [b4] at a2
  nlinarith

/-- **The archimedean lower bound with the printed error `6 log(12n)`**: for `n ≥ 1`,
`log κ_n - J_n + n (L_n - T_{2,n} - T_{3,n} - E) - 4 log 2 ≥ n (L_* - E) - 6 log(12n)`. -/
theorem kz_arch_source {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) {n : ℕ}
    (hn : 1 ≤ n) :
    n * (Real.log (4 + 3 * √3) - kzE) - 6 * Real.log (12 * n) ≤
      Real.log (kzKappa n) - kzJ μ n + n * (kzL l μ n - kzT2 l n - kzT3 μ n - kzE) -
        4 * Real.log 2 := by
  have h1 := kz_nL_ge hl hμ hn
  have h2 := kz_logKappa_sub_ge hl hμ hn
  have h3 := kzJ_le hμ hn
  have h4 := kz_brace_le hn
  have e : (n : ℝ) * (kzL l μ n - kzT2 l n - kzT3 μ n - kzE) =
      n * kzL l μ n - n * (kzT2 l n + kzT3 μ n) - n * kzE := by ring
  rw [e]
  nlinarith

/-! ### The endpoint difference and the slope -/

/-- **`|T_{2,n} - T_{3,n}| < 3/10`** for `n ≥ 250000`, from
`|T_{2,n} - T_{3,n}| ≤ (3/2) log 3 - 2 log 2 + 2 log(9n)/n`. -/
theorem abs_kzT2_sub_kzT3_lt {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) {n : ℕ}
    (hn : 250000 ≤ n) : |kzT2 l n - kzT3 μ n| < 3 / 10 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (250000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hD2lo, hD2hi⟩ := kzEndpointTwo_bounds hl n
  have hD3 := two_mul_kzEndpointThree hμ n
  have hT2 : (n : ℝ) * kzT2 l n = kzEndpointTwo l n * Real.log 2 := by
    rw [kzT2_eq, mul_div_assoc', mul_div_cancel_left₀ _ hn0.ne']
  have hT3 : (n : ℝ) * kzT3 μ n = kzEndpointThree μ n * Real.log 3 := by
    rw [kzT3_eq, mul_div_assoc', mul_div_cancel_left₀ _ hn0.ne']
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  obtain ⟨h1, h2, h3, h4, -, -, -, hδ, hδ0⟩ := kz_log_facts hμ hn1
  have hln : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have l23 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  have hs2 : (0 : ℝ) ≤ (Nat.digits 2 n).sum := Nat.cast_nonneg _
  have hs3 : (0 : ℝ) ≤ (Nat.digits 3 n).sum := Nat.cast_nonneg _
  have hs3' : (0 : ℝ) ≤ (Nat.digits 3 (2 * n + kzDelta μ)).sum := Nat.cast_nonneg _
  have p1 := mul_nonneg hs2 hl2.le
  have p2 := mul_nonneg hs3 hl3.le
  have p3 := mul_nonneg hs3' hl3.le
  have p4 := mul_nonneg hδ0 hl3.le
  have p5 := mul_le_mul_of_nonneg_right hδ hl3.le
  have hD2a := mul_le_mul_of_nonneg_right hD2lo hl2.le
  have hD2b := mul_le_mul_of_nonneg_right hD2hi hl2.le
  have hD3l : 2 * (kzEndpointThree μ n : ℝ) * Real.log 3 =
      (3 * n + kzDelta μ + (Nat.digits 3 n).sum - (Nat.digits 3 (2 * n + kzDelta μ)).sum) *
        Real.log 3 := by rw [hD3]
  have a2 : Real.log (3 * n + 1) ≤ 2 * Real.log 2 + Real.log n := by
    have : Real.log (3 * n + 1) ≤ Real.log (4 * n) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_mul (by norm_num) hn0.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at this
    push_cast at this
    linarith
  have a3 : Real.log (2 * n + kzDelta μ) ≤ Real.log 3 + Real.log n := by
    have : Real.log (2 * n + kzDelta μ) ≤ Real.log (3 * n) :=
      Real.log_le_log (by positivity) (by linarith)
    rwa [Real.log_mul (by norm_num) hn0.ne'] at this
  set c : ℝ := 3 / 2 * Real.log 3 - 2 * Real.log 2 with hc
  have hl3' := Real.log_three_lt_d9
  have hl3'' := Real.log_three_gt_d9
  have hl2' := Real.log_two_gt_d9
  have hl2'' := Real.log_two_lt_d9
  norm_num at hl3' hl3'' hl2' hl2''
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  have hc1 : c < 27 / 100 := by rw [hc]; linarith
  have hnc : 0 ≤ (n : ℝ) * c := mul_nonneg hn0.le hc0
  have hA : (n : ℝ) * (kzT3 μ n - kzT2 l n) ≤ n * c + (4 * Real.log 3 + 2 * Real.log n) := by
    rw [mul_sub, hT2, hT3, hc]
    linarith
  have hB : (n : ℝ) * (kzT2 l n - kzT3 μ n) ≤ n * c + (4 * Real.log 3 + 2 * Real.log n) := by
    have hB' : (n : ℝ) * (kzT2 l n - kzT3 μ n) ≤ -(n * c) + (4 * Real.log 3 + 2 * Real.log n) := by
      rw [mul_sub, hT2, hT3, hc]
      linarith
    linarith
  have hE : (4 * Real.log 3 + 2 * Real.log n) / n ≤ 30 / 250000 := by
    have e : 4 * Real.log 3 + 2 * Real.log n = 2 * Real.log (9 * n) := by
      rw [Real.log_mul (by norm_num) hn0.ne', show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    have h1log : 1 ≤ Real.log (9 * 250000) := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_d9]
    have hm := log_mul_div_le_of_le (c := 9) (n := n) (N := 250000) (by norm_num) (by norm_num)
      hnR h1log
    have h15 : Real.log (9 * 250000) < 15 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      linarith [exp_fifteen_gt]
    rw [e, mul_div_assoc]
    have : Real.log (9 * 250000) / 250000 ≤ 15 / 250000 :=
      div_le_div_of_nonneg_right h15.le (by norm_num)
    linarith
  have hupper : kzT3 μ n - kzT2 l n ≤ c + (4 * Real.log 3 + 2 * Real.log n) / n := by
    rw [add_div' _ _ _ hn0.ne', le_div_iff₀ hn0]
    linarith
  have hlower : kzT2 l n - kzT3 μ n ≤ c + (4 * Real.log 3 + 2 * Real.log n) / n := by
    rw [add_div' _ _ _ hn0.ne', le_div_iff₀ hn0]
    linarith
  rw [abs_lt]
  constructor <;> linarith

/-- **`L_* - E > 3/2`**, by the printed estimate: `√3 > 1.73` gives `4 + 3√3 > 9 · 919/900`,
and with `log 3 > 1.098`, `log 2 < 0.7` and `log(1+t) > t/(1+t)`,
`L_* - E > (5/3) (549/500) - 7/20 + 19/919 = 34478/22975 > 3/2`. -/
theorem kzLStar_sub_kzE_gt_three_halves : 3 / 2 < Real.log (4 + 3 * √3) - kzE := by
  have hs : (1.73 : ℝ) ≤ √3 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h1 : Real.log (9 * (919 / 900)) ≤ Real.log (4 + 3 * √3) :=
    Real.log_le_log (by norm_num) (by linarith)
  rw [Real.log_mul (by norm_num) (by norm_num)] at h1
  have h9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h2 : 1 - (919 / 900 : ℝ)⁻¹ ≤ Real.log (919 / 900) :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  have l2 : Real.log 2 < 0.7 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have l3 : (1.098 : ℝ) < Real.log 3 := lt_trans (by norm_num) Real.log_three_gt_d9
  norm_num at h2
  rw [kzE_eq]
  linarith

end ArithmeticOfJacobiPolynomials
