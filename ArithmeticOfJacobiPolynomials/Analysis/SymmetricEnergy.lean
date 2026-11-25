/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.SymmetricCoefficients
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Positivity

/-!
# The energy bound in the symmetric case (proof of Theorem 3.4)

For `f = P_{n+r}^{(r)}` and `λ = n(n+2r+1)` put `E = (1-x²) f'² + λ f²`
(Section 3.2 of the manuscript, proof of Theorem 3.4). We prove:

* `E' = 2(2r+1) x f'²` (`derivative_symmetricEnergy`), from the Gegenbauer equation;
* `E(x) ≥ E(0) = γ²` for every real `x` (`symmetricEnergy_ge`), in particular on `[-1,1]`;
* `γ² = λ f(0)² + f'(0)² > 0` for `n = 2m+δ`, `m ≥ 1` (`symmetric_gammaSq_pos`);
* `|h'(α)| > γ` at every real root `α ∈ (-1,1)`, `α ≠ 0`, of `h = f /ₘ x^δ`
  (`symmetric_gamma_lt_abs_derivative`);
* `b_m = 4^{-m} binom(2m,m) ≥ 1/(2√m)` for `m ≥ 1` (`one_div_two_mul_sqrt_le_centralBinom_div`);
* (3.16): `γ/f(1) = √(2m(2m+2r+1)) b_m/K` for `δ = 0`, `γ/f(1) = (2m+1) b_m/K` for `δ = 1`,
  with `K = binom(m+r,r)`, and `γ/f(1) > √m/K`.

Real values of rational polynomials are written `aeval x p`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-- **The energy identity.** For `f = P_{n+r}^{(r)}` and `λ = n(n+2r+1)`, the polynomial
`E = (1-x²) f'² + λ f²` satisfies `E' = 2(2r+1) x f'²`. -/
theorem derivative_symmetricEnergy (n r : ℕ) :
    derivative ((1 - X ^ 2) * (derivative (derivative^[r] (legendreP (n + r)))) ^ 2 +
        C ((n : ℚ) * (n + 2 * r + 1)) * (derivative^[r] (legendreP (n + r))) ^ 2) =
      C (2 * (2 * (r : ℚ) + 1)) * X * (derivative (derivative^[r] (legendreP (n + r)))) ^ 2 := by
  have ode := iterate_derivative_legendreP_differential_equation n r
  set f := derivative^[r] (legendreP (n + r))
  simp only [derivative_mul, derivative_add, derivative_sub, derivative_pow, derivative_one,
    derivative_X, derivative_C, zero_mul, zero_add, Nat.cast_ofNat]
  simp only [map_mul, map_add, map_ofNat, map_natCast, map_one] at ode ⊢
  linear_combination 2 * derivative f * ode

/-- A rational polynomial `P` with `P' = c x Q²`, `c ≥ 0`, attains its minimum over `ℝ` at `0`. -/
theorem aeval_zero_le_aeval_of_derivative_eq {P Q : ℚ[X]} {c : ℚ} (hc : 0 ≤ c)
    (hP : derivative P = C c * X * Q ^ 2) (x : ℝ) :
    aeval (0 : ℝ) P ≤ aeval x P := by
  have hd : ∀ t : ℝ, deriv (fun y : ℝ => aeval y P) t = (c : ℝ) * t * (aeval t Q) ^ 2 := by
    intro t
    rw [Polynomial.deriv_aeval, hP]
    simp [map_mul, aeval_C, aeval_X, map_pow, eq_ratCast]
  have hdiff : Differentiable ℝ fun y : ℝ => aeval y P := Polynomial.differentiable_aeval P
  have hcont : Continuous fun y : ℝ => aeval y P := hdiff.continuous
  have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
  rcases le_total 0 x with hx | hx
  · refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont.continuousOn hdiff.differentiableOn
      (fun t ht => ?_) (Set.mem_Ici.mpr le_rfl) hx hx
    rw [interior_Ici] at ht
    rw [hd]
    have : (0 : ℝ) < t := ht
    positivity
  · refine antitoneOn_of_deriv_nonpos (convex_Iic 0) hcont.continuousOn hdiff.differentiableOn
      (fun t ht => ?_) hx (Set.mem_Iic.mpr le_rfl) hx
    rw [interior_Iic] at ht
    rw [hd]
    have : t < 0 := ht
    have h1 : 0 ≤ (c : ℝ) * (aeval t Q) ^ 2 := by positivity
    nlinarith

/-- **The energy bound.** For `f = P_{n+r}^{(r)}`, `λ = n(n+2r+1)` and every real `x`,
`E(x) = (1-x²) f'(x)² + λ f(x)² ≥ E(0) = λ f(0)² + f'(0)² = γ²`. -/
theorem symmetricEnergy_ge (n r : ℕ) (x : ℝ) :
    (n : ℝ) * (n + 2 * r + 1) * (aeval (0 : ℝ) (derivative^[r] (legendreP (n + r)))) ^ 2 +
        (aeval (0 : ℝ) (derivative (derivative^[r] (legendreP (n + r))))) ^ 2 ≤
      (1 - x ^ 2) * (aeval x (derivative (derivative^[r] (legendreP (n + r))))) ^ 2 +
        (n : ℝ) * (n + 2 * r + 1) * (aeval x (derivative^[r] (legendreP (n + r)))) ^ 2 := by
  have h := aeval_zero_le_aeval_of_derivative_eq (by positivity) (derivative_symmetricEnergy n r) x
  simp only [map_mul, map_add, map_sub, map_pow, aeval_C, aeval_X, eq_ratCast, map_one,
    Rat.cast_natCast, Rat.cast_ofNat] at h
  linarith

theorem aeval_zero_eq_coeff_zero (p : ℚ[X]) : aeval (0 : ℝ) p = (p.coeff 0 : ℝ) := by
  rw [← coeff_zero_eq_aeval_zero' (A := ℝ) p, eq_ratCast]

theorem aeval_zero_derivative_eq_coeff_one (p : ℚ[X]) :
    aeval (0 : ℝ) (derivative p) = (p.coeff 1 : ℝ) := by
  rw [aeval_zero_eq_coeff_zero, coeff_derivative]
  simp

theorem aeval_one_eq_eval_one (p : ℚ[X]) : aeval (1 : ℝ) p = ((p.eval 1 : ℚ) : ℝ) := by
  have := aeval_algebraMap_apply_eq_algebraMap_eval (A := ℝ) (1 : ℚ) p
  simpa [eq_ratCast] using this

/-- **Positivity of `γ²`.** For `n = 2m+δ`, `δ ∈ {0,1}`, `m ≥ 1` and `f = P_{n+r}^{(r)}`,
`γ² = λ f(0)² + f'(0)² > 0`. -/
theorem symmetric_gammaSq_pos (m r δ : ℕ) (hm : 1 ≤ m) (hδ : δ ≤ 1) :
    0 < ((2 * m + δ : ℕ) : ℝ) * ((2 * m + δ : ℕ) + 2 * r + 1) *
        (aeval (0 : ℝ) (derivative^[r] (legendreP (2 * m + δ + r)))) ^ 2 +
      (aeval (0 : ℝ) (derivative (derivative^[r] (legendreP (2 * m + δ + r))))) ^ 2 := by
  have hc := coeff_iterate_derivative_legendreP_center m r δ hδ
  have hne : (derivative^[r] (legendreP (2 * m + δ + r))).coeff δ ≠ 0 := by
    rw [hc]
    have : ((2 * m + 2 * r + 2 * δ - 1).doubleFactorial : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.doubleFactorial_pos _).ne'
    exact mul_ne_zero (div_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)) this
  rw [aeval_zero_eq_coeff_zero, aeval_zero_derivative_eq_coeff_one]
  interval_cases δ
  · have h1 : (0 : ℝ) < ((2 * m + 0 : ℕ) : ℝ) * ((2 * m + 0 : ℕ) + 2 * r + 1) := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      push_cast; nlinarith
    have h2 : (0 : ℝ) < (((derivative^[r] (legendreP (2 * m + 0 + r))).coeff 0 : ℚ) : ℝ) ^ 2 := by
      have : (((derivative^[r] (legendreP (2 * m + 0 + r))).coeff 0 : ℚ) : ℝ) ≠ 0 := by
        exact_mod_cast hne
      positivity
    have := mul_pos h1 h2
    positivity
  · have h2 : (0 : ℝ) < (((derivative^[r] (legendreP (2 * m + 1 + r))).coeff 1 : ℚ) : ℝ) ^ 2 := by
      have : (((derivative^[r] (legendreP (2 * m + 1 + r))).coeff 1 : ℚ) : ℝ) ≠ 0 := by
        exact_mod_cast hne
      positivity
    have h3 : (0 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) * ((2 * m + 1 : ℕ) + 2 * r + 1) *
        (((derivative^[r] (legendreP (2 * m + 1 + r))).coeff 0 : ℚ) : ℝ) ^ 2 := by positivity
    linarith

/-- **The root derivative bound.** Let `n = 2m+δ`, `δ ∈ {0,1}`, `m ≥ 1`, `f = P_{n+r}^{(r)}`,
`h = f /ₘ x^δ` and `γ = √(λ f(0)² + f'(0)²)`, `λ = n(n+2r+1)`. At every real root
`α ∈ (-1,1)`, `α ≠ 0`, of `h` we have `|h'(α)| > γ`. -/
theorem symmetric_gamma_lt_abs_derivative (m r δ : ℕ) (hm : 1 ≤ m) (hδ : δ ≤ 1) {α : ℝ}
    (hα : α ∈ Set.Ioo (-1 : ℝ) 1) (hα0 : α ≠ 0)
    (hroot : aeval α (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ X ^ δ) = 0) :
    Real.sqrt (((2 * m + δ : ℕ) : ℝ) * ((2 * m + δ : ℕ) + 2 * r + 1) *
        (aeval (0 : ℝ) (derivative^[r] (legendreP (2 * m + δ + r)))) ^ 2 +
      (aeval (0 : ℝ) (derivative (derivative^[r] (legendreP (2 * m + δ + r))))) ^ 2) <
      |aeval α (derivative (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ X ^ δ))| := by
  have hpos := symmetric_gammaSq_pos m r δ hm hδ
  have hE := symmetricEnergy_ge (2 * m + δ) r α
  have hfac := X_pow_mul_iterate_derivative_legendreP_divByMonic m r δ hδ
  set f := derivative^[r] (legendreP (2 * m + δ + r))
  set h := f /ₘ X ^ δ
  set G := ((2 * m + δ : ℕ) : ℝ) * ((2 * m + δ : ℕ) + 2 * r + 1) * (aeval (0 : ℝ) f) ^ 2 +
      (aeval (0 : ℝ) (derivative f)) ^ 2
  have hf0 : aeval α f = 0 := by
    rw [← hfac, map_mul, hroot, mul_zero]
  have hf1 : aeval α (derivative f) = α ^ δ * aeval α (derivative h) := by
    rw [← hfac, derivative_mul, map_add, map_mul, map_mul, hroot, mul_zero, zero_add,
      map_pow, aeval_X]
  rw [hf0, hf1] at hE
  obtain ⟨ha1, ha2⟩ := hα
  have hs : 0 < 1 - α ^ 2 := by nlinarith
  have hs1 : 1 - α ^ 2 < 1 := by have := pow_pos (abs_pos.mpr hα0) 2; rw [sq_abs] at this; linarith
  have hpow : (α ^ δ) ^ 2 ≤ 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact pow_le_one₀ (sq_nonneg α) (by nlinarith)
  have hG : G ≤ (1 - α ^ 2) * (α ^ δ) ^ 2 * (aeval α (derivative h)) ^ 2 := by
    have : G ≤ (1 - α ^ 2) * (α ^ δ * aeval α (derivative h)) ^ 2 +
        ((2 * m + δ : ℕ) : ℝ) * ((2 * m + δ : ℕ) + 2 * r + 1) * 0 ^ 2 := by
      convert hE using 3
    linarith [mul_pow (α ^ δ) (aeval α (derivative h)) 2]
  have hd2 : 0 < (aeval α (derivative h)) ^ 2 := by
    by_contra hcon
    have : (aeval α (derivative h)) ^ 2 = 0 := le_antisymm (not_lt.mp hcon) (sq_nonneg _)
    rw [this, mul_zero] at hG
    linarith
  have hlt : G < (aeval α (derivative h)) ^ 2 := by
    have h3 : (1 - α ^ 2) * (α ^ δ) ^ 2 < 1 := by
      have : (1 - α ^ 2) * (α ^ δ) ^ 2 ≤ (1 - α ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hpow hs.le
      linarith
    calc G ≤ (1 - α ^ 2) * (α ^ δ) ^ 2 * (aeval α (derivative h)) ^ 2 := hG
      _ < 1 * (aeval α (derivative h)) ^ 2 := mul_lt_mul_of_pos_right h3 hd2
      _ = _ := one_mul _
  calc Real.sqrt G < Real.sqrt ((aeval α (derivative h)) ^ 2) :=
        Real.sqrt_lt_sqrt hpos.le hlt
    _ = |aeval α (derivative h)| := Real.sqrt_sq_eq_abs _

/-- `4^{2m} ≤ 4m binom(2m,m)²` for `m ≥ 1`. -/
theorem four_pow_two_mul_le_centralBinom_sq (m : ℕ) (hm : 1 ≤ m) :
    4 ^ (2 * m) ≤ 4 * m * (Nat.centralBinom m) ^ 2 := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have key : (m + 1) * (4 * (m + 1) * (Nat.centralBinom (m + 1)) ^ 2) =
        16 * (2 * m + 1) ^ 2 * (Nat.centralBinom m) ^ 2 := by
      have h := Nat.succ_mul_centralBinom_succ m
      calc (m + 1) * (4 * (m + 1) * (Nat.centralBinom (m + 1)) ^ 2)
          = 4 * ((m + 1) * Nat.centralBinom (m + 1)) ^ 2 := by ring
        _ = _ := by rw [h]; ring
    have hle : (m + 1) * 4 ^ (2 * (m + 1)) ≤
        (m + 1) * (4 * (m + 1) * (Nat.centralBinom (m + 1)) ^ 2) := by
      rw [key]
      have h1 : (m + 1) * 4 ^ (2 * (m + 1)) = 16 * ((m + 1) * 4 ^ (2 * m)) := by ring
      have h2 : 4 * m * (m + 1) ≤ (2 * m + 1) ^ 2 := by nlinarith
      rw [h1]
      calc 16 * ((m + 1) * 4 ^ (2 * m)) ≤ 16 * ((m + 1) * (4 * m * (Nat.centralBinom m) ^ 2)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ih)
        _ = 16 * (4 * m * (m + 1)) * (Nat.centralBinom m) ^ 2 := by ring
        _ ≤ 16 * (2 * m + 1) ^ 2 * (Nat.centralBinom m) ^ 2 :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)
    exact Nat.le_of_mul_le_mul_left hle (Nat.succ_pos m)

/-- **`b_m ≥ 1/(2√m)`.** For `m ≥ 1`, `b_m = 4^{-m} binom(2m,m) ≥ 1/(2√m)` (proof of
Lemma 3.2). -/
theorem one_div_two_mul_sqrt_le_centralBinom_div (m : ℕ) (hm : 1 ≤ m) :
    1 / (2 * Real.sqrt m) ≤ ((2 * m).choose m : ℝ) / 4 ^ m := by
  have h := four_pow_two_mul_le_centralBinom_sq m hm
  rw [Nat.centralBinom_eq_two_mul_choose] at h
  have h' : (4 : ℝ) ^ (2 * m) ≤ 4 * m * ((2 * m).choose m : ℝ) ^ 2 := by exact_mod_cast h
  set b : ℝ := ((2 * m).choose m : ℝ) / 4 ^ m
  have hb : 0 ≤ b := by positivity
  have h4 : (0 : ℝ) < 4 ^ m := by positivity
  have hsq : 1 ≤ 4 * m * b ^ 2 := by
    have : 4 * (m : ℝ) * b ^ 2 = 4 * m * ((2 * m).choose m : ℝ) ^ 2 / 4 ^ (2 * m) := by
      simp only [b]; rw [pow_mul']; field_simp
    rw [this, le_div_iff₀ (by positivity)]
    linarith
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm'
  have hss : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm'.le
  rw [div_le_iff₀ (by positivity)]
  have hx : 0 ≤ b * (2 * Real.sqrt m) := by positivity
  have hx2 : 1 ≤ (b * (2 * Real.sqrt m)) ^ 2 := by
    calc (1 : ℝ) ≤ 4 * m * b ^ 2 := hsq
      _ = (b * (2 * Real.sqrt m)) ^ 2 := by rw [mul_pow, mul_pow, hss]; ring
  nlinarith

/-- **Eq. (3.16), `δ = 0`.** For `f = P_{2m+r}^{(r)}`, `λ = 2m(2m+2r+1)` and
`γ = √(λ f(0)² + f'(0)²)`: `γ / f(1) = √(2m(2m+2r+1)) b_m / K`, with `b_m = 4^{-m} binom(2m,m)`
and `K = binom(m+r, r)`. -/
theorem symmetric_gamma_div_eval_one_even (m r : ℕ) :
    Real.sqrt ((2 * m : ℝ) * (2 * m + 2 * r + 1) *
        (aeval (0 : ℝ) (derivative^[r] (legendreP (2 * m + r)))) ^ 2 +
      (aeval (0 : ℝ) (derivative (derivative^[r] (legendreP (2 * m + r))))) ^ 2) /
      aeval (1 : ℝ) (derivative^[r] (legendreP (2 * m + r))) =
    Real.sqrt ((2 * m : ℝ) * (2 * m + 2 * r + 1)) * (((2 * m).choose m : ℝ) / 4 ^ m) /
      ((m + r).choose r : ℝ) := by
  have hc := coeff_iterate_derivative_legendreP_center m r 0 (Nat.zero_le _)
  simp only [add_zero, mul_zero] at hc
  have h1 : (derivative^[r] (legendreP (2 * m + r))).coeff 1 = 0 :=
    coeff_iterate_derivative_legendreP_eq_zero_of_odd (2 * m) r 1 ⟨m, rfl⟩
  have he := eval_one_iterate_derivative_legendreP (2 * m) r
  rw [aeval_zero_eq_coeff_zero, aeval_zero_derivative_eq_coeff_one, aeval_one_eq_eval_one, h1,
    hc, he, Rat.cast_zero, zero_pow two_ne_zero, add_zero, Real.sqrt_mul (by positivity),
    Real.sqrt_sq_eq_abs, mul_div_assoc, mul_div_assoc]
  congr 1
  have hK := Nat.choose_mul_factorial_mul_factorial (n := m + r) (k := r) (by omega)
  rw [show m + r - r = m by omega] at hK
  have hK' : ((m + r).choose r : ℝ) * (r.factorial : ℝ) * (m.factorial : ℝ) =
      ((m + r).factorial : ℝ) := by exact_mod_cast hK
  have hC := Nat.choose_mul_factorial_mul_factorial (n := 2 * m) (k := m) (by omega)
  rw [show 2 * m - m = m by omega] at hC
  have hC' : ((2 * m).choose m : ℝ) * (m.factorial : ℝ) * (m.factorial : ℝ) =
      ((2 * m).factorial : ℝ) := by exact_mod_cast hC
  have hF : (((2 * m + 2 * r).factorial : ℕ) : ℝ) =
      2 ^ (m + r) * (m + r).factorial * (2 * m + 2 * r - 1).doubleFactorial := by
    rw [show 2 * m + 2 * r = 2 * (m + r) by ring]
    exact_mod_cast factorial_two_mul_eq (m + r)
  have h4 : (4 : ℝ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
  push_cast
  rw [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast, abs_of_pos
    (by positivity : (0 : ℝ) < 2 ^ m * (m.factorial : ℝ)), hF, ← hK', ← hC', h4, pow_add]
  have : (m.factorial : ℝ) ≠ 0 := by positivity
  have : (r.factorial : ℝ) ≠ 0 := by positivity
  have : ((m + r).choose r : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have : ((2 * m).choose m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have : ((2 * m + 2 * r - 1).doubleFactorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos _).ne'
  field_simp

/-- **Eq. (3.16), `δ = 1`.** For `f = P_{2m+1+r}^{(r)}`, `λ = (2m+1)(2m+2r+2)` and
`γ = √(λ f(0)² + f'(0)²)`: `γ / f(1) = (2m+1) b_m / K`, with `b_m = 4^{-m} binom(2m,m)` and
`K = binom(m+r, r)`. -/
theorem symmetric_gamma_div_eval_one_odd (m r : ℕ) :
    Real.sqrt ((2 * m + 1 : ℝ) * (2 * m + 1 + 2 * r + 1) *
        (aeval (0 : ℝ) (derivative^[r] (legendreP (2 * m + 1 + r)))) ^ 2 +
      (aeval (0 : ℝ) (derivative (derivative^[r] (legendreP (2 * m + 1 + r))))) ^ 2) /
      aeval (1 : ℝ) (derivative^[r] (legendreP (2 * m + 1 + r))) =
    (2 * m + 1 : ℝ) * (((2 * m).choose m : ℝ) / 4 ^ m) / ((m + r).choose r : ℝ) := by
  have hc := coeff_iterate_derivative_legendreP_center m r 1 le_rfl
  have h0 : (derivative^[r] (legendreP (2 * m + 1 + r))).coeff 0 = 0 :=
    coeff_iterate_derivative_legendreP_eq_zero_of_odd (2 * m + 1) r 0 ⟨m, rfl⟩
  have he := eval_one_iterate_derivative_legendreP (2 * m + 1) r
  rw [aeval_zero_eq_coeff_zero, aeval_zero_derivative_eq_coeff_one, aeval_one_eq_eval_one, h0,
    hc, he, Rat.cast_zero, zero_pow two_ne_zero, mul_zero, zero_add, Real.sqrt_sq_eq_abs,
    mul_div_assoc]
  have hK := Nat.choose_mul_factorial_mul_factorial (n := m + r) (k := r) (by omega)
  rw [show m + r - r = m by omega] at hK
  have hK' : ((m + r).choose r : ℝ) * (r.factorial : ℝ) * (m.factorial : ℝ) =
      ((m + r).factorial : ℝ) := by exact_mod_cast hK
  have hC := Nat.choose_mul_factorial_mul_factorial (n := 2 * m) (k := m) (by omega)
  rw [show 2 * m - m = m by omega] at hC
  have hC' : ((2 * m).choose m : ℝ) * (m.factorial : ℝ) * (m.factorial : ℝ) =
      ((2 * m).factorial : ℝ) := by exact_mod_cast hC
  have hF : (((2 * m + 1 + 2 * r).factorial : ℕ) : ℝ) =
      (2 * m + 2 * r + 1) * (2 ^ (m + r) * (m + r).factorial *
        (2 * (m + r) - 1).doubleFactorial) := by
    rw [show 2 * m + 1 + 2 * r = 2 * (m + r) + 1 by ring, Nat.factorial_succ]
    push_cast
    rw [factorial_two_mul_eq (m + r)]
    push_cast
    ring
  have hD : (((2 * m + 2 * r + 1).doubleFactorial : ℕ) : ℝ) =
      (2 * m + 2 * r + 1) * (2 * (m + r) - 1).doubleFactorial := by
    rw [show 2 * m + 2 * r + 1 = 2 * (m + r) + 1 by omega,
      doubleFactorial_two_mul_add_one]
    push_cast
    ring
  have hF1 : (((2 * m + 1).factorial : ℕ) : ℝ) = (2 * m + 1) * (2 * m).factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have h4 : (4 : ℝ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
  push_cast
  rw [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast, abs_of_pos
    (by positivity : (0 : ℝ) < 2 ^ m * (m.factorial : ℝ)), hF, hD, hF1, ← hK', ← hC', h4,
    pow_add]
  have : (m.factorial : ℝ) ≠ 0 := by positivity
  have : (r.factorial : ℝ) ≠ 0 := by positivity
  have : ((m + r).choose r : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have : ((2 * m).choose m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have : ((2 * (m + r) - 1).doubleFactorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos _).ne'
  field_simp

/-- **Eq. (3.16), the comparison.** For `n = 2m+δ`, `δ ∈ {0,1}`, `m ≥ 1`, `f = P_{n+r}^{(r)}`,
`λ = n(n+2r+1)` and `γ = √(λ f(0)² + f'(0)²)`: `γ / f(1) > √m / K`, `K = binom(m+r, r)`. -/
theorem sqrt_div_choose_lt_symmetric_gamma_div_eval_one (m r δ : ℕ) (hm : 1 ≤ m)
    (hδ : δ ≤ 1) :
    Real.sqrt m / ((m + r).choose r : ℝ) <
      Real.sqrt (((2 * m + δ : ℕ) : ℝ) * ((2 * m + δ : ℕ) + 2 * r + 1) *
          (aeval (0 : ℝ) (derivative^[r] (legendreP (2 * m + δ + r)))) ^ 2 +
        (aeval (0 : ℝ) (derivative (derivative^[r] (legendreP (2 * m + δ + r))))) ^ 2) /
        aeval (1 : ℝ) (derivative^[r] (legendreP (2 * m + δ + r))) := by
  have hb := one_div_two_mul_sqrt_le_centralBinom_div m hm
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by linarith)
  have hss : Real.sqrt m ^ 2 = m := Real.sq_sqrt (by linarith)
  have hK : (0 : ℝ) < ((m + r).choose r : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hb' : 1 ≤ ((2 * m).choose m : ℝ) / 4 ^ m * (2 * Real.sqrt m) := by
    rwa [div_le_iff₀ (by positivity)] at hb
  interval_cases δ
  · simp only [add_zero, Nat.cast_mul, Nat.cast_ofNat]
    rw [symmetric_gamma_div_eval_one_even]
    refine div_lt_div_of_pos_right ?_ hK
    have hL : 2 * (m : ℝ) < Real.sqrt ((2 * m : ℝ) * (2 * m + 2 * r + 1)) := by
      rw [Real.lt_sqrt (by positivity)]
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      nlinarith
    nlinarith [Real.sqrt_nonneg ((2 * m : ℝ) * (2 * m + 2 * r + 1))]
  · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [symmetric_gamma_div_eval_one_odd]
    refine div_lt_div_of_pos_right ?_ hK
    nlinarith

end ArithmeticOfJacobiPolynomials
