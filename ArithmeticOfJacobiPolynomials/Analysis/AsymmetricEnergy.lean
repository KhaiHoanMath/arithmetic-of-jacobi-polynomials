/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.DifferentialEquation
public import ArithmeticOfJacobiPolynomials.Jacobi.CentralValue
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The energy bound in the asymmetric case (proof of Theorem 3.1)

For integers `a > b ≥ 0` put `s = a + b`, `q = a - b`, `f = P_n^{(a,b)}`, `λ = n(n+s+1)` and
`E = (1-x²) f'² + λ f²` (proof of Theorem 3.1, the energy paragraph). We prove:

* `E' = 2(q + (s+1)x) f'²` (`derivative_asymmetricEnergy`), from the Jacobi equation;
* `E(x) ≥ E(x₀)` for every real `x`, `x₀ = -q/(s+1)` (sign of `E'`);
* `E(x₀) ≥ c_{a,b}² E(0)` with `c_{a,b} = (s+1)^{s+1} / √((2a+1)^{2a+1} (2b+1)^{2b+1})`
  (`asymmetricEnergyConstant`): the polynomial `G = E (1-x)^{2a+1} (1+x)^{2b+1}` has
  `G' = -2λ (q + (s+1)x) f² (1-x)^{2a} (1+x)^{2b}`, so `G(x₀) ≥ G(0) = E(0)`, and
  `(1-x₀)^{2a+1} (1+x₀)^{2b+1} = (2a+1)^{2a+1} (2b+1)^{2b+1} / (s+1)^{2s+2}`;
* `|f'(α)| > c_{a,b} √m / D_δ(m)` at every root `α ∈ (-1,1)` of `f = P_{2m+δ}^{(a,b)}`, when
  `m ≥ 1` and `A_δ(m) ≠ 0` (`asymmetric_gamma_lt_abs_derivative`), from Lemma 3.2 and
  `λ ≥ 4m²`.

Real values of rational polynomials are written `aeval x p`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-- `E = (1-x²) f'² + λ f²` for `f = P_n^{(a,b)}` and `λ = n(n+a+b+1)`. -/
noncomputable def asymmetricEnergy (a b n : ℕ) : ℚ[X] :=
  (1 - X ^ 2) * (derivative (jacobiP a b n)) ^ 2 +
    C ((n : ℚ) * (n + a + b + 1)) * (jacobiP a b n) ^ 2

theorem asymmetricEnergy_eq (a b n : ℕ) : asymmetricEnergy a b n =
    (1 - X ^ 2) * (derivative (jacobiP a b n)) ^ 2 +
      C ((n : ℚ) * (n + a + b + 1)) * (jacobiP a b n) ^ 2 := (rfl)

/-- **The energy identity.** `E' = 2(q + (s+1)x) f'²`, with `q = a - b`, `s = a + b`. -/
theorem derivative_asymmetricEnergy (a b n : ℕ) :
    derivative (asymmetricEnergy a b n) =
      C 2 * (C ((a : ℚ) - b) + C ((a : ℚ) + b + 1) * X) * (derivative (jacobiP a b n)) ^ 2 := by
  have ode := jacobiP_ode (a : ℚ) b n
  rw [asymmetricEnergy_eq]
  simp only [derivative_mul, derivative_add, derivative_sub, derivative_pow, derivative_one,
    derivative_X, derivative_C, zero_mul, zero_add, Nat.cast_ofNat]
  simp only [map_mul, map_add, map_sub, map_ofNat, map_natCast, map_one] at ode ⊢
  linear_combination 2 * derivative (jacobiP (a : ℚ) b n) * ode

theorem derivative_one_sub_X_pow (a : ℕ) :
    derivative ((1 - X : ℚ[X]) ^ (2 * a + 1)) = -(C (2 * (a : ℚ) + 1) * ((1 - X) ^ a) ^ 2) := by
  rw [derivative_pow, Nat.add_sub_cancel, pow_mul', derivative_sub, derivative_one,
    derivative_X]
  simp only [map_add, map_mul, map_natCast, map_ofNat, map_one, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one]
  ring

theorem derivative_one_add_X_pow (b : ℕ) :
    derivative ((1 + X : ℚ[X]) ^ (2 * b + 1)) = C (2 * (b : ℚ) + 1) * ((1 + X) ^ b) ^ 2 := by
  rw [derivative_pow, Nat.add_sub_cancel, pow_mul', derivative_add, derivative_one,
    derivative_X]
  simp only [map_add, map_mul, map_natCast, map_ofNat, map_one, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one]
  ring

/-- **The weighted energy identity.** For `G = E (1-x)^{2a+1} (1+x)^{2b+1}`,
`(-G)' = 2λ (q + (s+1)x) (f (1-x)^a (1+x)^b)²`. -/
theorem derivative_asymmetricWeightedEnergy (a b n : ℕ) :
    derivative (-(asymmetricEnergy a b n * (1 - X) ^ (2 * a + 1) * (1 + X) ^ (2 * b + 1))) =
      C (2 * ((n : ℚ) * (n + a + b + 1))) * (C ((a : ℚ) - b) + C ((a : ℚ) + b + 1) * X) *
        (jacobiP a b n * (1 - X) ^ a * (1 + X) ^ b) ^ 2 := by
  have hE := derivative_asymmetricEnergy a b n
  have e1 : (1 - X : ℚ[X]) ^ (2 * a + 1) = ((1 - X) ^ a) ^ 2 * (1 - X) := by
    rw [pow_succ, pow_mul']
  have e2 : (1 + X : ℚ[X]) ^ (2 * b + 1) = ((1 + X) ^ b) ^ 2 * (1 + X) := by
    rw [pow_succ, pow_mul']
  rw [derivative_neg, derivative_mul, derivative_mul, hE, derivative_one_sub_X_pow,
    derivative_one_add_X_pow, e1, e2, asymmetricEnergy_eq]
  generalize (1 - X : ℚ[X]) ^ a = u
  generalize (1 + X : ℚ[X]) ^ b = v
  simp only [map_sub, map_add, map_mul, map_natCast, map_ofNat, map_one]
  ring

/-- A rational polynomial `P` with `P' = c (u + v x) Q²`, `c ≥ 0`, `v > 0`, attains its minimum
over `ℝ` at `x₀ = -u/v`. -/
theorem aeval_le_of_derivative_eq_mul_linear {P Q : ℚ[X]} {c u v : ℚ} (hc : 0 ≤ c)
    (hv : 0 < v) (hP : derivative P = C c * (C u + C v * X) * Q ^ 2) (x : ℝ) :
    aeval (-(u : ℝ) / v) P ≤ aeval x P := by
  have hd : ∀ t : ℝ, deriv (fun y : ℝ => aeval y P) t =
      (c : ℝ) * (u + v * t) * (aeval t Q) ^ 2 := by
    intro t
    rw [Polynomial.deriv_aeval, hP]
    simp [map_mul, aeval_C, aeval_X, map_pow, eq_ratCast]
  have hdiff : Differentiable ℝ fun y : ℝ => aeval y P := Polynomial.differentiable_aeval P
  have hcont : Continuous fun y : ℝ => aeval y P := hdiff.continuous
  have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hvne : (v : ℝ) ≠ 0 := hv'.ne'
  have hx0 : (v : ℝ) * (-(u : ℝ) / v) = -u := by field_simp
  generalize -(u : ℝ) / v = x0 at hx0 ⊢
  rcases le_total x0 x with hx | hx
  · refine monotoneOn_of_deriv_nonneg (convex_Ici _) hcont.continuousOn hdiff.differentiableOn
      (fun t ht => ?_) (Set.mem_Ici.mpr le_rfl) hx hx
    rw [interior_Ici] at ht
    rw [hd]
    have ht' : x0 < t := ht
    have h1 : 0 ≤ (u : ℝ) + v * t := by nlinarith
    exact mul_nonneg (mul_nonneg hc' h1) (sq_nonneg _)
  · refine antitoneOn_of_deriv_nonpos (convex_Iic _) hcont.continuousOn hdiff.differentiableOn
      (fun t ht => ?_) hx (Set.mem_Iic.mpr le_rfl) hx
    rw [interior_Iic] at ht
    rw [hd]
    have ht' : t < x0 := ht
    have h1 : (u : ℝ) + v * t ≤ 0 := by nlinarith
    have h2 : 0 ≤ (c : ℝ) * (aeval t Q) ^ 2 := mul_nonneg hc' (sq_nonneg _)
    nlinarith

theorem aeval_asymmetricEnergy (a b n : ℕ) (x : ℝ) : aeval x (asymmetricEnergy a b n) =
    (1 - x ^ 2) * (aeval x (derivative (jacobiP a b n))) ^ 2 +
      (n : ℝ) * (n + a + b + 1) * (aeval x (jacobiP a b n)) ^ 2 := by
  rw [asymmetricEnergy_eq]
  simp only [map_mul, map_add, map_sub, map_pow, aeval_C, aeval_X, eq_ratCast, map_one]
  push_cast
  ring

/-- `c_{a,b} = (s+1)^{s+1} / √((2a+1)^{2a+1} (2b+1)^{2b+1})`, `s = a + b`. -/
noncomputable def asymmetricEnergyConstant (a b : ℕ) : ℝ :=
  ((a + b + 1 : ℝ)) ^ (a + b + 1) /
    Real.sqrt ((2 * a + 1 : ℝ) ^ (2 * a + 1) * (2 * b + 1 : ℝ) ^ (2 * b + 1))

theorem asymmetricEnergyConstant_eq (a b : ℕ) : asymmetricEnergyConstant a b =
    ((a + b + 1 : ℝ)) ^ (a + b + 1) /
      Real.sqrt ((2 * a + 1 : ℝ) ^ (2 * a + 1) * (2 * b + 1 : ℝ) ^ (2 * b + 1)) := (rfl)

theorem asymmetricEnergyConstant_pos (a b : ℕ) : 0 < asymmetricEnergyConstant a b := by
  rw [asymmetricEnergyConstant_eq]
  positivity

theorem asymmetricEnergyConstant_sq (a b : ℕ) : asymmetricEnergyConstant a b ^ 2 =
    ((a + b + 1 : ℝ)) ^ (2 * (a + b + 1)) /
      ((2 * a + 1 : ℝ) ^ (2 * a + 1) * (2 * b + 1 : ℝ) ^ (2 * b + 1)) := by
  rw [asymmetricEnergyConstant_eq, div_pow, Real.sq_sqrt (by positivity), ← pow_mul,
    mul_comm (a + b + 1) 2]

/-- **The root derivative bound** (proof of Theorem 3.1). Let `a > b ≥ 0`, `δ ∈ {0,1}`,
`m ≥ 1` with `A_δ(m) ≠ 0`, and `f = P_{2m+δ}^{(a,b)}`. At every root `α ∈ (-1,1)` of `f`,
`|f'(α)| > c_{a,b} √m / D_δ(m)`. -/
theorem asymmetric_gamma_lt_abs_derivative (a b m δ : ℕ) (hab : b < a) (hδ : δ ≤ 1)
    (hm : 1 ≤ m) (hA : (centralA a b δ).eval (m : ℤ) ≠ 0) {α : ℝ}
    (hα : α ∈ Set.Ioo (-1 : ℝ) 1) (hroot : aeval α (jacobiP a b (2 * m + δ)) = 0) :
    asymmetricEnergyConstant a b * Real.sqrt m / (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ) <
      |aeval α (derivative (jacobiP a b (2 * m + δ)))| := by
  have hs : 0 ≤ 1 - α ^ 2 := by
    obtain ⟨h1, h2⟩ := hα
    nlinarith
  have hD : (0 : ℝ) < (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ) := by
    have := centralD_eval_pos a b δ m
    exact_mod_cast this
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hss : Real.sqrt (m : ℝ) ^ 2 = m := Real.sq_sqrt (by linarith)
  have hKpos := asymmetricEnergyConstant_pos a b
  have hlow := one_div_le_abs_jacobiP_eval_zero a b m δ hab hδ hm hA
  have hf0 : aeval (0 : ℝ) (jacobiP a b (2 * m + δ)) =
      (((jacobiP a b (2 * m + δ)).eval 0 : ℚ) : ℝ) := by
    have := aeval_algebraMap_apply_eq_algebraMap_eval (A := ℝ) (0 : ℚ) (jacobiP a b (2 * m + δ))
    simpa [eq_ratCast] using this
  rw [← hf0] at hlow
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [hroot, abs_zero] at hlow
    have : 0 < 1 / (2 * Real.sqrt m * (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ)) :=
      one_div_pos.mpr (mul_pos (mul_pos two_pos hsm) hD)
    linarith
  have hmin := aeval_le_of_derivative_eq_mul_linear (by norm_num) (by positivity)
    (derivative_asymmetricEnergy a b (2 * m + δ)) α
  have hG := aeval_le_of_derivative_eq_mul_linear (by positivity) (by positivity)
    (derivative_asymmetricWeightedEnergy a b (2 * m + δ)) 0
  generalize hx : -((((a : ℚ) - b : ℚ)) : ℝ) / ((((a : ℚ) + b + 1 : ℚ)) : ℝ) = x0 at hmin hG
  simp only [map_neg, map_mul, map_pow, map_sub, map_add, map_one, aeval_X, sub_zero, add_zero,
    one_pow, mul_one, neg_le_neg_iff] at hG
  rw [aeval_asymmetricEnergy a b (2 * m + δ) 0] at hG
  rw [aeval_asymmetricEnergy a b (2 * m + δ) α, hroot] at hmin
  have hs1 : (0 : ℝ) < a + b + 1 := by positivity
  have h1x : 1 - x0 = (2 * a + 1) / (a + b + 1) := by
    rw [← hx, eq_div_iff hs1.ne']
    push_cast
    rw [sub_mul, div_mul_cancel₀ _ hs1.ne']
    ring
  have h2x : 1 + x0 = (2 * b + 1) / (a + b + 1) := by
    rw [← hx, eq_div_iff hs1.ne']
    push_cast
    rw [add_mul, div_mul_cancel₀ _ hs1.ne']
    ring
  have hKW : asymmetricEnergyConstant a b ^ 2 *
      ((1 - x0) ^ (2 * a + 1) * (1 + x0) ^ (2 * b + 1)) = 1 := by
    rw [asymmetricEnergyConstant_sq, h1x, h2x, div_pow, div_pow]
    have hS : ((a + b + 1 : ℝ)) ^ (2 * (a + b + 1)) =
        (a + b + 1 : ℝ) ^ (2 * a + 1) * (a + b + 1 : ℝ) ^ (2 * b + 1) := by
      rw [← pow_add]
      congr 1
      ring
    rw [hS, div_mul_div_comm, div_mul_div_comm, div_eq_one_iff_eq (by positivity)]
    ring
  have hlam : 4 * (m : ℝ) ^ 2 ≤
      ((2 * m + δ : ℕ) : ℝ) * (((2 * m + δ : ℕ) : ℝ) + a + b + 1) := by
    push_cast
    have : (0 : ℝ) ≤ δ := Nat.cast_nonneg δ
    have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    nlinarith
  have hα2 : 0 < α ^ 2 := lt_of_le_of_ne (sq_nonneg α) (Ne.symm (pow_ne_zero 2 hα0))
  generalize aeval α (derivative (jacobiP (a : ℚ) (b : ℚ) (2 * m + δ))) = Fa at hmin ⊢
  generalize aeval (0 : ℝ) (derivative (jacobiP (a : ℚ) (b : ℚ) (2 * m + δ))) = F10 at hG
  generalize aeval (0 : ℝ) (jacobiP (a : ℚ) (b : ℚ) (2 * m + δ)) = F0 at hG hlow
  generalize aeval x0 (asymmetricEnergy a b (2 * m + δ)) = Ex0 at hmin hG
  generalize (1 - x0) ^ (2 * a + 1) = W1 at hG hKW
  generalize (1 + x0) ^ (2 * b + 1) = W2 at hG hKW
  generalize ((2 * m + δ : ℕ) : ℝ) * (((2 * m + δ : ℕ) : ℝ) + a + b + 1) = L at hG hlam hmin
  generalize asymmetricEnergyConstant a b = K at hKW hKpos ⊢
  generalize (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ) = D at hD hlow ⊢
  generalize Real.sqrt (m : ℝ) = s0 at hlow hss hsm ⊢
  rw [div_le_iff₀ (mul_pos (mul_pos two_pos hsm) hD)] at hlow
  have h4 : 1 ≤ F0 ^ 2 * (2 ^ 2 * m * D ^ 2) := by
    have := one_le_pow₀ hlow (n := 2)
    rw [mul_pow, mul_pow, mul_pow, sq_abs, hss] at this
    exact this
  have hE0 : L * F0 ^ 2 ≤ Ex0 * W1 * W2 := by nlinarith [sq_nonneg F10]
  have h5 : K ^ 2 * (L * F0 ^ 2) ≤ Ex0 :=
    calc K ^ 2 * (L * F0 ^ 2) ≤ K ^ 2 * (Ex0 * W1 * W2) :=
          mul_le_mul_of_nonneg_left hE0 (sq_nonneg K)
      _ = Ex0 * (K ^ 2 * (W1 * W2)) := by ring
      _ = Ex0 := by rw [hKW, mul_one]
  have h6 : K ^ 2 * (L * F0 ^ 2) ≤ (1 - α ^ 2) * Fa ^ 2 := by nlinarith
  have h7 : (m : ℝ) ≤ L * F0 ^ 2 * D ^ 2 := by
    have hm0 : (0 : ℝ) ≤ m := by linarith
    have a1 : (m : ℝ) * 1 ≤ m * (F0 ^ 2 * (2 ^ 2 * m * D ^ 2)) :=
      mul_le_mul_of_nonneg_left h4 hm0
    have a2 : 4 * (m : ℝ) ^ 2 * (F0 ^ 2 * D ^ 2) ≤ L * (F0 ^ 2 * D ^ 2) :=
      mul_le_mul_of_nonneg_right hlam (by positivity)
    nlinarith
  have h8 : K ^ 2 * m ≤ D ^ 2 * ((1 - α ^ 2) * Fa ^ 2) :=
    calc K ^ 2 * m ≤ K ^ 2 * (L * F0 ^ 2 * D ^ 2) := mul_le_mul_of_nonneg_left h7 (sq_nonneg K)
      _ = D ^ 2 * (K ^ 2 * (L * F0 ^ 2)) := by ring
      _ ≤ D ^ 2 * ((1 - α ^ 2) * Fa ^ 2) := mul_le_mul_of_nonneg_left h6 (sq_nonneg D)
  have hKm : 0 < K ^ 2 * m := mul_pos (pow_pos hKpos 2) (by linarith)
  have hFa : 0 < Fa ^ 2 := by
    rcases (sq_nonneg Fa).lt_or_eq with h | h
    · exact h
    · rw [← h] at h8
      nlinarith
  have h9 : D ^ 2 * ((1 - α ^ 2) * Fa ^ 2) < D ^ 2 * Fa ^ 2 := by
    have := mul_pos (mul_pos (pow_pos hD 2) hα2) hFa
    linarith [mul_nonneg (mul_nonneg (sq_nonneg D) hs) hFa.le]
  have h10 : (K * s0) ^ 2 < (D * |Fa|) ^ 2 := by
    rw [mul_pow, mul_pow, hss, sq_abs]
    linarith
  have h11 := lt_of_pow_lt_pow_left₀ 2 (mul_nonneg hD.le (abs_nonneg _)) h10
  rw [div_lt_iff₀ hD]
  linarith

end ArithmeticOfJacobiPolynomials
