/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Central values of Jacobi polynomials with integral parameters (Lemma 3.2)

For integers `a > b ≥ 0`, put `q = a - b`, and for `δ ∈ {0,1}`
`H_δ = ⌊(q-δ)/2⌋`, `K_δ = b + δ + H_δ` (3.4),
`D_δ(z) = 2^δ ∏_{j=1}^{K_δ} (z+j)` (3.5) and
`A_δ(z) = (∏_{j=1}^{b+δ}(2z+j)) ∑_{h=0}^{H_δ} (-1)^h binom(q, δ+2h) z^{\underline h}
  ∏_{j=b+δ+h+1}^{K_δ}(z+j)` (3.6).
Lemma 3.2: `P_{2m+δ}^{(a,b)}(0) = (-1)^m b_m A_δ(m)/D_δ(m)` with
`b_m = 4^{-m} binom(2m,m)`; if `m ≥ 1` and `A_δ(m) ≠ 0` then
`|P_{2m+δ}^{(a,b)}(0)| ≥ 1/(2√m D_δ(m))`; each parity has only finitely many zero central
values.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset
open scoped Nat

/-- `H_δ = ⌊(q - δ)/2⌋` of (3.4), for `q = a - b ≥ 1` and `δ ∈ {0,1}`. -/
def centralH (a b δ : ℕ) : ℕ := (a - b - δ) / 2

/-- `K_δ = b + δ + H_δ` of (3.4). -/
def centralK (a b δ : ℕ) : ℕ := b + δ + centralH a b δ

/-- `D_δ(z) = 2^δ ∏_{j=1}^{K_δ} (z + j)` of (3.5). -/
noncomputable def centralD (a b δ : ℕ) : ℤ[X] :=
  C (2 ^ δ) * ∏ j ∈ Icc 1 (centralK a b δ), (X + C (j : ℤ))

/-- `A_δ(z)` of (3.6); `descPochhammer ℤ h` is the falling factorial `z^{\underline h}`. -/
noncomputable def centralA (a b δ : ℕ) : ℤ[X] :=
  (∏ j ∈ Icc 1 (b + δ), (C 2 * X + C (j : ℤ))) *
    ∑ h ∈ range (centralH a b δ + 1),
      C ((-1) ^ h * ((a - b).choose (δ + 2 * h) : ℤ)) * descPochhammer ℤ h *
        ∏ j ∈ Icc (b + δ + h + 1) (centralK a b δ), (X + C (j : ℤ))

theorem centralH_eq (a b δ : ℕ) : centralH a b δ = (a - b - δ) / 2 := (rfl)
theorem centralK_eq (a b δ : ℕ) : centralK a b δ = b + δ + centralH a b δ := (rfl)
theorem centralD_eq (a b δ : ℕ) :
    centralD a b δ = C (2 ^ δ) * ∏ j ∈ Icc 1 (centralK a b δ), (X + C (j : ℤ)) := (rfl)
theorem centralA_eq (a b δ : ℕ) : centralA a b δ =
    (∏ j ∈ Icc 1 (b + δ), (C 2 * X + C (j : ℤ))) *
      ∑ h ∈ range (centralH a b δ + 1),
        C ((-1) ^ h * ((a - b).choose (δ + 2 * h) : ℤ)) * descPochhammer ℤ h *
          ∏ j ∈ Icc (b + δ + h + 1) (centralK a b δ), (X + C (j : ℤ)) := (rfl)

/-- `∏_{j=c+1}^{K} (x + j) · (x + c)! = (x + K)!`. -/
theorem prod_Icc_add_mul_factorial (x c K : ℕ) (hcK : c ≤ K) :
    (∏ j ∈ Icc (c + 1) K, (x + j)) * (x + c)! = (x + K)! := by
  rw [Finset.Icc_add_one_left_eq_Ioc]
  induction K, hcK using Nat.le_induction with
  | base => simp
  | succ K hK ih =>
    rw [Finset.prod_Ioc_succ_top hK, mul_right_comm, ih, ← add_assoc, Nat.factorial_succ]
    ring

/-- The value at `0`: `P_n^{(a,b)}(0) = 2^{-n} ∑_j (-1)^j binom(n+a, n-j) binom(n+b, j)`. -/
theorem jacobiP_eval_zero_nat (a b n : ℕ) : (jacobiP a b n).eval 0 =
    (1 / 2 : ℚ) ^ n * ∑ j ∈ range (n + 1),
      (-1) ^ j * ((n + a).choose (n - j) : ℚ) * ((n + b).choose j : ℚ) := by
  rw [jacobiP_eq, eval_mul, eval_C, eval_finsetSum]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_add, eval_X, eval_one, zero_sub,
    zero_add, one_pow, mul_one]
  rw [show ((n : ℚ) + (a : ℚ)) = ((n + a : ℕ) : ℚ) by push_cast; ring,
    show ((n : ℚ) + (b : ℚ)) = ((n + b : ℕ) : ℚ) by push_cast; ring,
    Ring.choose_natCast, Ring.choose_natCast]
  ring

/-- `(1 - X^k)^N = ∑_l (-1)^l binom(N,l) X^{kl}`. -/
theorem one_sub_X_pow_pow (N k : ℕ) : ((1 : ℚ[X]) - X ^ k) ^ N =
    ∑ l ∈ range (N + 1), C ((-1) ^ l * (N.choose l : ℚ)) * X ^ (k * l) := by
  rw [show ((1 : ℚ[X]) - X ^ k) = -X ^ k + 1 by ring, add_pow]
  refine sum_congr rfl fun l _ => ?_
  rw [one_pow, mul_one, neg_pow, ← pow_mul, C_mul, C_pow, C_neg, C_1, ← C_eq_natCast,
    mul_comm k l]
  ring

/-- Coefficients of `(X+1)^e ∑_l c_l X^{kl}`. -/
theorem coeff_X_add_one_pow_mul_sum (e d k L : ℕ) (c : ℕ → ℚ) :
    ((X + 1) ^ e * ∑ l ∈ range L, C (c l) * X ^ (k * l)).coeff d =
      ∑ l ∈ range L, c l * if k * l ≤ d then (e.choose (d - k * l) : ℚ) else 0 := by
  rw [mul_sum, finsetSum_coeff]
  refine sum_congr rfl fun l _ => ?_
  rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_X_add_one_pow]

/-- The generating-function identity behind (3.3)'s proof:
`∑_j (-1)^j binom(n+a,n-j) binom(n+b,j) = ∑_{l ≤ m} (-1)^l binom(n+b,l) binom(q, n-2l)`. -/
theorem sum_choose_eq_sum_choose (b q m δ : ℕ) (hδ : δ ≤ 1) :
    ∑ j ∈ range (2 * m + δ + 1), (-1) ^ j * ((2 * m + δ + (b + q)).choose (2 * m + δ - j) : ℚ) *
        ((2 * m + δ + b).choose j : ℚ) =
      ∑ l ∈ range (m + 1), (-1) ^ l * ((2 * m + δ + b).choose l : ℚ) *
        (q.choose (2 * m + δ - 2 * l) : ℚ) := by
  set n := 2 * m + δ
  have key : (((X : ℚ[X]) + 1) ^ (n + (b + q)) * (1 - X ^ 1) ^ (n + b)).coeff n =
      (((X : ℚ[X]) + 1) ^ q * (1 - X ^ 2) ^ (n + b)).coeff n := by
    congr 1
    rw [show n + (b + q) = q + (n + b) by ring, pow_add, mul_assoc, ← mul_pow]
    congr 2
    ring
  rw [one_sub_X_pow_pow, one_sub_X_pow_pow, coeff_X_add_one_pow_mul_sum,
    coeff_X_add_one_pow_mul_sum] at key
  have hL : ∑ l ∈ range (n + b + 1), (-1) ^ l * ((n + b).choose l : ℚ) *
      (if 1 * l ≤ n then ((n + (b + q)).choose (n - 1 * l) : ℚ) else 0) =
      ∑ j ∈ range (n + 1), (-1) ^ j * ((n + (b + q)).choose (n - j) : ℚ) *
        ((n + b).choose j : ℚ) := by
    rw [← sum_subset (range_subset_range.mpr (show n + 1 ≤ n + b + 1 by omega))
      (fun l _ hl => ?_)]
    · refine sum_congr rfl fun l hl => ?_
      rw [mem_range] at hl
      rw [ite_eq_left_iff.mpr (fun h => absurd (by omega) h), one_mul]; ring
    · rw [mem_range] at hl
      rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]; ring
  have hR : ∑ l ∈ range (n + b + 1), (-1) ^ l * ((n + b).choose l : ℚ) *
      (if 2 * l ≤ n then (q.choose (n - 2 * l) : ℚ) else 0) =
      ∑ l ∈ range (m + 1), (-1) ^ l * ((n + b).choose l : ℚ) * (q.choose (n - 2 * l) : ℚ) := by
    rw [← sum_subset (range_subset_range.mpr (show m + 1 ≤ n + b + 1 by omega))
      (fun l _ hl => ?_)]
    · refine sum_congr rfl fun l hl => ?_
      rw [mem_range] at hl
      rw [ite_eq_left_iff.mpr (fun h => absurd (by omega) h)]
    · rw [mem_range] at hl
      rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]; ring
  simp only [mul_assoc] at key hL hR ⊢
  rw [← hL, key, hR]

/-- The identity `binom(2m+δ+b, m-h) / binom(2m,m) =
∏_{j=1}^{b+δ}(2m+j) m^{\underline h} / ∏_{j=1}^{b+δ+h}(m+j)` from the proof of Lemma 3.2,
multiplied out by `∏_{j=1}^{K}(m+j)`. -/
theorem choose_mul_prod_Icc_eq (m b δ h K : ℕ) (hK : b + δ + h ≤ K) (hh : h ≤ m) :
    (2 * m + δ + b).choose (m - h) * ∏ j ∈ Icc 1 K, (m + j) =
      (2 * m).choose m * (∏ j ∈ Icc 1 (b + δ), (2 * m + j)) * m.descFactorial h *
        ∏ j ∈ Icc (b + δ + h + 1) K, (m + j) := by
  have E1 := Nat.choose_mul_factorial_mul_factorial (show m - h ≤ 2 * m + δ + b by omega)
  rw [show 2 * m + δ + b - (m - h) = m + (b + δ + h) by omega,
    show 2 * m + δ + b = 2 * m + (b + δ) by ring] at E1
  have E2 := prod_Icc_add_mul_factorial m 0 K (Nat.zero_le _)
  rw [zero_add, add_zero] at E2
  have E3 := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
  rw [show 2 * m - m = m by omega] at E3
  have E4 := prod_Icc_add_mul_factorial (2 * m) 0 (b + δ) (Nat.zero_le _)
  rw [zero_add, add_zero] at E4
  have E5 := Nat.factorial_mul_descFactorial hh
  have E6 := prod_Icc_add_mul_factorial m (b + δ + h) K hK
  rw [show 2 * m + δ + b = 2 * m + (b + δ) by ring]
  apply Nat.eq_of_mul_eq_mul_right (show 0 < m ! * (m - h)! * (m + (b + δ + h))! by positivity)
  apply Nat.cast_injective (R := ℤ)
  have E1' : (((2 * m + (b + δ)).choose (m - h) : ℕ) : ℤ) * ((m - h)! : ℕ) *
      ((m + (b + δ + h))! : ℕ) = ((2 * m + (b + δ))! : ℕ) := by exact_mod_cast E1
  have E2' : ((∏ j ∈ Icc 1 K, (m + j) : ℕ) : ℤ) * (m ! : ℕ) = ((m + K)! : ℕ) := by
    exact_mod_cast E2
  have E3' : (((2 * m).choose m : ℕ) : ℤ) * (m ! : ℕ) * (m ! : ℕ) = ((2 * m)! : ℕ) := by
    exact_mod_cast E3
  have E4' : ((∏ j ∈ Icc 1 (b + δ), (2 * m + j) : ℕ) : ℤ) * ((2 * m)! : ℕ) =
      ((2 * m + (b + δ))! : ℕ) := by exact_mod_cast E4
  have E5' : (((m - h)! : ℕ) : ℤ) * (m.descFactorial h : ℕ) = (m ! : ℕ) := by exact_mod_cast E5
  have E6' : ((∏ j ∈ Icc (b + δ + h + 1) K, (m + j) : ℕ) : ℤ) * ((m + (b + δ + h))! : ℕ) =
      ((m + K)! : ℕ) := by exact_mod_cast E6
  push_cast [Nat.cast_mul]
  generalize (((2 * m + (b + δ)).choose (m - h) : ℕ) : ℤ) = c1 at *
  generalize (((m - h)! : ℕ) : ℤ) = f1 at *
  generalize (((m + (b + δ + h))! : ℕ) : ℤ) = f2 at *
  generalize (((2 * m + (b + δ))! : ℕ) : ℤ) = Fnb at *
  generalize ((m ! : ℕ) : ℤ) = fm at *
  generalize (((m + K)! : ℕ) : ℤ) = FmK at *
  generalize (((2 * m).choose m : ℕ) : ℤ) = c2 at *
  generalize (((2 * m)! : ℕ) : ℤ) = F2m at *
  generalize ((m.descFactorial h : ℕ) : ℤ) = dF at *
  push_cast at E2' E4' E6'
  generalize (∏ j ∈ Icc 1 K, ((m : ℤ) + (j : ℤ))) = pK at *
  generalize (∏ j ∈ Icc 1 (b + δ), (2 * (m : ℤ) + (j : ℤ))) = p2 at *
  generalize (∏ j ∈ Icc (b + δ + h + 1) K, ((m : ℤ) + (j : ℤ))) = pc at *
  linear_combination (pK * fm) * E1' + Fnb * E2' - (c2 * p2 * fm * pc * f2) * E5' -
    (c2 * p2 * fm * fm) * E6' - (p2 * FmK) * E3' - FmK * E4'

theorem centralD_eval (a b δ m : ℕ) : (((centralD a b δ).eval (m : ℤ) : ℤ) : ℚ) =
    2 ^ δ * ((∏ j ∈ Icc 1 (centralK a b δ), (m + j) : ℕ) : ℚ) := by
  rw [centralD_eq, eval_mul, eval_C, eval_prod]
  simp only [eval_add, eval_X, eval_C]
  push_cast
  rfl

theorem centralA_eval (a b δ m : ℕ) : (((centralA a b δ).eval (m : ℤ) : ℤ) : ℚ) =
    ((∏ j ∈ Icc 1 (b + δ), (2 * m + j) : ℕ) : ℚ) *
      ∑ h ∈ range (centralH a b δ + 1), (-1) ^ h * ((a - b).choose (δ + 2 * h) : ℚ) *
        (m.descFactorial h : ℚ) *
          ((∏ j ∈ Icc (b + δ + h + 1) (centralK a b δ), (m + j) : ℕ) : ℚ) := by
  rw [centralA_eq, eval_mul, eval_prod, eval_finsetSum]
  simp only [eval_mul, eval_C, eval_prod, eval_add, eval_X, descPochhammer_eval_eq_descFactorial]
  push_cast
  rfl

/-- `D_δ(m) > 0`. -/
theorem centralD_eval_pos (a b δ m : ℕ) : 0 < (((centralD a b δ).eval (m : ℤ) : ℤ) : ℚ) := by
  rw [centralD_eval]
  have : 0 < ∏ j ∈ Icc 1 (centralK a b δ), (m + j) :=
    Finset.prod_pos fun j hj => by simp at hj; omega
  positivity

/-- **Lemma 3.2, central-value formula (3.7).** For integers `a > b ≥ 0`, `δ ∈ {0,1}` and
`m ≥ 0`, `P_{2m+δ}^{(a,b)}(0) = (-1)^m b_m A_δ(m) / D_δ(m)` with `b_m = 4^{-m} binom(2m, m)`. -/
theorem jacobiP_eval_zero_eq_central (a b m δ : ℕ) (hab : b < a) (hδ : δ ≤ 1) :
    (jacobiP a b (2 * m + δ)).eval 0 =
      (-1) ^ m * ((1 / 4 : ℚ) ^ m * ((2 * m).choose m : ℚ)) *
        (((centralA a b δ).eval (m : ℤ) : ℤ) : ℚ) / (((centralD a b δ).eval (m : ℤ) : ℤ) : ℚ) := by
  obtain ⟨q, rfl⟩ : ∃ q, a = b + q := ⟨a - b, by omega⟩
  have hq : b + q - b = q := by omega
  rw [eq_div_iff (centralD_eval_pos _ _ _ _).ne', centralA_eval, centralD_eval,
    jacobiP_eval_zero_nat, sum_choose_eq_sum_choose b q m δ hδ, hq]
  set H := centralH (b + q) b δ with hH
  set K := centralK (b + q) b δ with hK
  have hHq : δ + 2 * H ≤ q := by rw [hH, centralH_eq]; omega
  have hHq' : q < δ + 2 * (H + 1) := by rw [hH, centralH_eq]; omega
  have hKH : K = b + δ + H := by rw [hK, centralK_eq]
  set pK : ℚ := ((∏ j ∈ Icc 1 K, (m + j) : ℕ) : ℚ)
  set T : ℕ → ℚ := fun h => if h ≤ m then (-1) ^ (m - h) *
    ((2 * m + δ + b).choose (m - h) : ℚ) * (q.choose (δ + 2 * h) : ℚ) * pK else 0 with hT
  have hT1 : (∑ l ∈ range (m + 1), (-1) ^ l * ((2 * m + δ + b).choose l : ℚ) *
      (q.choose (2 * m + δ - 2 * l) : ℚ)) * pK = ∑ h ∈ range (m + H + 1), T h := by
    rw [sum_mul, ← Finset.sum_range_reflect, ← sum_subset
      (range_subset_range.mpr (show m + 1 ≤ m + H + 1 by omega)) (fun h _ hh => ?_)]
    · refine sum_congr rfl fun h hh => ?_
      rw [mem_range] at hh
      rw [hT]
      simp only
      rw [ite_eq_left_iff.mpr (fun h' => absurd (by omega) h'), show m + 1 - 1 - h = m - h by omega,
        show 2 * m + δ - 2 * (m - h) = δ + 2 * h by omega]
    · rw [mem_range] at hh
      rw [hT]; simp only; rw [ite_eq_right_iff.mpr (fun h' => absurd h' (by omega))]
  have hT2 : (-1) ^ m * ((2 * m).choose m : ℚ) *
      (((∏ j ∈ Icc 1 (b + δ), (2 * m + j) : ℕ) : ℚ) *
        ∑ h ∈ range (H + 1), (-1) ^ h * (q.choose (δ + 2 * h) : ℚ) *
          (m.descFactorial h : ℚ) * ((∏ j ∈ Icc (b + δ + h + 1) K, (m + j) : ℕ) : ℚ)) =
      ∑ h ∈ range (m + H + 1), T h := by
    rw [mul_sum, mul_sum, ← sum_subset
      (range_subset_range.mpr (show H + 1 ≤ m + H + 1 by omega)) (fun h _ hh => ?_)]
    · refine sum_congr rfl fun h hh => ?_
      rw [mem_range] at hh
      rw [hT]
      simp only
      split_ifs with hm
      · have key := choose_mul_prod_Icc_eq m b δ h K (by omega) hm
        have key' : ((2 * m + δ + b).choose (m - h) : ℚ) * pK =
            ((2 * m).choose m : ℚ) * ((∏ j ∈ Icc 1 (b + δ), (2 * m + j) : ℕ) : ℚ) *
              (m.descFactorial h : ℚ) *
              ((∏ j ∈ Icc (b + δ + h + 1) K, (m + j) : ℕ) : ℚ) := by
          have := congrArg (Nat.cast : ℕ → ℚ) key
          simpa only [Nat.cast_mul] using this
        have hsign : ((-1 : ℚ) ^ m) = (-1) ^ (m - h) * (-1) ^ h := by
          rw [← pow_add, Nat.sub_add_cancel hm]
        have hsq : ((-1 : ℚ) ^ h) * (-1) ^ h = 1 := by
          rw [← pow_add, ← two_mul, pow_mul]; norm_num
        rw [mul_assoc ((-1) ^ (m - h) * _), mul_comm ((q.choose (δ + 2 * h) : ℚ)),
          ← mul_assoc ((-1) ^ (m - h) * _), mul_assoc ((-1) ^ (m - h)), key', hsign]
        linear_combination ((-1) ^ (m - h) * ((2 * m).choose m : ℚ) *
          ((∏ j ∈ Icc 1 (b + δ), (2 * m + j) : ℕ) : ℚ) * (m.descFactorial h : ℚ) *
          ((∏ j ∈ Icc (b + δ + h + 1) K, (m + j) : ℕ) : ℚ) *
          (q.choose (δ + 2 * h) : ℚ)) * hsq
      · rw [(Nat.descFactorial_eq_zero_iff_lt).mpr (by omega)]
        simp
    · rw [mem_range] at hh
      rw [hT]; simp only
      rw [Nat.choose_eq_zero_of_lt (n := q) (k := δ + 2 * h) (by omega)]
      simp
  have h2 : (1 / 2 : ℚ) ^ (2 * m + δ) * 2 ^ δ = (1 / 4) ^ m := by
    rw [pow_add, pow_mul, mul_assoc, ← mul_pow]; norm_num
  calc (1 / 2 : ℚ) ^ (2 * m + δ) * (∑ l ∈ range (m + 1), (-1) ^ l *
        ((2 * m + δ + b).choose l : ℚ) * (q.choose (2 * m + δ - 2 * l) : ℚ)) * (2 ^ δ * pK)
      = ((1 / 2 : ℚ) ^ (2 * m + δ) * 2 ^ δ) * ((∑ l ∈ range (m + 1), (-1) ^ l *
        ((2 * m + δ + b).choose l : ℚ) * (q.choose (2 * m + δ - 2 * l) : ℚ)) * pK) := by ring
    _ = (1 / 4) ^ m * ∑ h ∈ range (m + H + 1), T h := by rw [h2, hT1]
    _ = _ := by rw [← hT2]; ring

/-- `A_δ(0) > 0` (stated after (3.6)). -/
theorem centralA_eval_zero_pos (a b δ : ℕ) (hab : b < a) (hδ : δ ≤ 1) :
    0 < (centralA a b δ).eval 0 := by
  have h := centralA_eval a b δ 0
  rw [Nat.cast_zero] at h
  rw [sum_eq_single 0 (fun h' _ h0 => by
    rw [Nat.descFactorial_of_lt (by omega)]; simp) (fun h0 => by simp at h0)] at h
  have h1 : 0 < ∏ j ∈ Icc 1 (b + δ), (2 * 0 + j) :=
    prod_pos fun j hj => by simp at hj; omega
  have h2 : 0 < ∏ j ∈ Icc (b + δ + 0 + 1) (centralK a b δ), (0 + j) :=
    prod_pos fun j hj => by simp at hj; omega
  have h3 : 0 < (a - b).choose (δ + 2 * 0) := Nat.choose_pos (by omega)
  have : (0 : ℚ) < (((centralA a b δ).eval 0 : ℤ) : ℚ) := by
    rw [h]
    simp only [pow_zero, one_mul, Nat.descFactorial_zero, Nat.cast_one, mul_one]
    have h3' : (0 : ℚ) < ((a - b).choose (δ + 2 * 0) : ℚ) := by exact_mod_cast h3
    positivity
  exact_mod_cast this

/-- `16^m ≤ 4m binom(2m,m)²` for `m ≥ 1`, i.e. `b_m ≥ 1/(2√m)`. -/
theorem sixteen_pow_le_four_mul_choose_sq (m : ℕ) (hm : 1 ≤ m) :
    16 ^ m ≤ 4 * m * ((2 * m).choose m) ^ 2 := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have hrec := Nat.succ_mul_centralBinom_succ m
    rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at hrec
    set B := (2 * m).choose m
    set B' := (2 * (m + 1)).choose (m + 1)
    have hsq : (m + 1) * (4 * (m + 1) * B' ^ 2) = 16 * (2 * m + 1) ^ 2 * B ^ 2 := by
      have : ((m + 1) * B') ^ 2 = (2 * (2 * m + 1) * B) ^ 2 := by rw [hrec]
      nlinarith [this]
    have hineq : (m + 1) * 16 ^ (m + 1) ≤ (m + 1) * (4 * (m + 1) * B' ^ 2) := by
      rw [hsq, pow_succ]
      have h4 : 4 * m * (m + 1) ≤ (2 * m + 1) ^ 2 := by nlinarith
      calc (m + 1) * (16 ^ m * 16) ≤ (m + 1) * (4 * m * B ^ 2 * 16) := by gcongr
        _ = 16 * (4 * m * (m + 1)) * B ^ 2 := by ring
        _ ≤ 16 * (2 * m + 1) ^ 2 * B ^ 2 := by gcongr
    exact Nat.le_of_mul_le_mul_left hineq (by omega)

/-- **Lemma 3.2, lower bound.** If `m ≥ 1` and `A_δ(m) ≠ 0`, then
`|P_{2m+δ}^{(a,b)}(0)| ≥ 1/(2√m D_δ(m))`. -/
theorem one_div_le_abs_jacobiP_eval_zero (a b m δ : ℕ) (hab : b < a) (hδ : δ ≤ 1)
    (hm : 1 ≤ m) (hA : (centralA a b δ).eval (m : ℤ) ≠ 0) :
    1 / (2 * Real.sqrt m * (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ)) ≤
      |(((jacobiP a b (2 * m + δ)).eval 0 : ℚ) : ℝ)| := by
  rw [jacobiP_eval_zero_eq_central a b m δ hab hδ]
  set A := (centralA a b δ).eval (m : ℤ)
  set D := (centralD a b δ).eval (m : ℤ)
  have hD : (0 : ℝ) < D := by
    have := centralD_eval_pos a b δ m
    exact_mod_cast this
  have hA1 : (1 : ℝ) ≤ |(A : ℝ)| := by
    have := Int.one_le_abs hA
    exact_mod_cast this
  have hbin := sixteen_pow_le_four_mul_choose_sq m hm
  set B := (2 * m).choose m
  have hbm : 1 ≤ 2 * Real.sqrt m * ((1 / 4 : ℝ) ^ m * B) := by
    have hB : (16 : ℝ) ^ m ≤ 4 * m * (B : ℝ) ^ 2 := by exact_mod_cast hbin
    have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) m)
    have hs0 := Real.sqrt_nonneg (m : ℝ)
    have h16 : (16 : ℝ) ^ m * ((1 / 4 : ℝ) ^ m) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm m 2, pow_mul, ← mul_pow]; norm_num
    have hx : 1 ≤ (2 * Real.sqrt m * ((1 / 4 : ℝ) ^ m * B)) ^ 2 := by
      have : (2 * Real.sqrt m * ((1 / 4 : ℝ) ^ m * B)) ^ 2 =
          4 * m * (B : ℝ) ^ 2 * ((1 / 4 : ℝ) ^ m) ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, hs]; ring
      rw [this]
      calc (1 : ℝ) = 16 ^ m * ((1 / 4 : ℝ) ^ m) ^ 2 := h16.symm
        _ ≤ 4 * m * (B : ℝ) ^ 2 * ((1 / 4 : ℝ) ^ m) ^ 2 := by gcongr
    have h0 : 0 ≤ 2 * Real.sqrt m * ((1 / 4 : ℝ) ^ m * B) := by positivity
    nlinarith
  push_cast
  rw [abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos hD, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 4) ^ m * B)]
  rw [div_le_div_iff₀ (by positivity) hD]
  nlinarith [mul_le_mul hbm hA1 zero_le_one (by positivity)]

/-- **Lemma 3.2, finiteness.** For each parity `δ`, only finitely many `m` give a zero central
value `P_{2m+δ}^{(a,b)}(0) = 0`. -/
theorem setOf_jacobiP_eval_zero_finite (a b δ : ℕ) (hab : b < a) (hδ : δ ≤ 1) :
    {m : ℕ | (jacobiP a b (2 * m + δ)).eval 0 = 0}.Finite := by
  have hA0 : centralA a b δ ≠ 0 := fun h => by
    have := centralA_eval_zero_pos a b δ hab hδ
    rw [h, eval_zero] at this
    exact lt_irrefl _ this
  refine ((finite_setOfPred_isRoot hA0).preimage Nat.cast_injective.injOn).subset fun m hm => ?_
  simp only [Set.mem_ofPred_eq] at hm
  rw [jacobiP_eval_zero_eq_central a b m δ hab hδ] at hm
  have hD := (centralD_eval_pos a b δ m).ne'
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, IsRoot.def]
  rcases div_eq_zero_iff.mp hm with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h (pow_ne_zero _ (by norm_num))
      · exfalso
        have : (0 : ℚ) < (1 / 4) ^ m * ((2 * m).choose m : ℚ) := by
          have := Nat.choose_pos (show m ≤ 2 * m by omega)
          positivity
        exact this.ne' h
    · exact_mod_cast h
  · exact absurd h hD

end ArithmeticOfJacobiPolynomials
