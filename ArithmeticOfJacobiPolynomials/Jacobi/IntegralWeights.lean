/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.Wronskian
public import ArithmeticOfJacobiPolynomials.Jacobi.SourceStieltjesRational
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integral weights (Lemma 2.3)

For integers `a, b ≥ 0` and `n ≥ 1` the functional
`I(g) = ∫_{-1}^0 g(t) (-t)^a (t+1)^b dt` has the rational moments
`ν_j = I(t^j) = (-1)^j (j+a)! b! / (j+a+b+1)!`; it acts coefficientwise on polynomials over
any field of characteristic zero. With `Q = P_n^{(a,b)}(2X+1) / binom(n+a, a)`,
`V(X) = I_t((Q(X) - Q(t))/(X - t))` and `p₀ = X(X+1)` we prove:

* the root identity (2.10): `p₀(z) Q'(z) V(z) = 𝒞_n` at every root `z` of `Q`, where
  `𝒞_n = -(a!)² n! (n+b)! / ((n+a)! (n+a+b)!)`;
* the moment valuation bound (2.9): `v_p(ν_j) ≥ -⌊log_p(j+a+b+1)⌋`;
* orthogonality `I(t^j Q) = 0` for `j < n`, and the integral formula for `ν_j`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-! ### The moments -/

/-- The moments `ν_j = (-1)^j (j+a)! b! / (j+a+b+1)!` of
`I(g) = ∫_{-1}^0 g(t) (-t)^a (t+1)^b dt`. -/
noncomputable def integralWeightMoment (a b j : ℕ) : ℚ :=
  (-1) ^ j * ((j + a).factorial * b.factorial : ℚ) / (j + a + b + 1).factorial

theorem integralWeightMoment_eq (a b j : ℕ) : integralWeightMoment a b j =
    (-1) ^ j * ((j + a).factorial * b.factorial : ℚ) / (j + a + b + 1).factorial := (rfl)

/-- The functional `I` of Section 2.3, acting coefficientwise. -/
noncomputable def integralWeightFunctional (a b : ℕ) : ℚ[X] →ₗ[ℚ] ℚ :=
  momentFunctional (integralWeightMoment a b)

theorem integralWeightFunctional_eq (a b : ℕ) :
    integralWeightFunctional a b = momentFunctional (integralWeightMoment a b) := (rfl)

/-- The alternating sum `∑_k (-1)^k binom(b,k)/(m+k+1) = m! b!/(m+b+1)!` (a Beta integral). -/
theorem sum_neg_one_pow_choose_div (m b : ℕ) :
    ∑ k ∈ range (b + 1), (-1 : ℚ) ^ k * (b.choose k : ℚ) / ((m : ℚ) + k + 1) =
      (m.factorial * b.factorial : ℚ) / (m + b + 1).factorial := by
  induction b generalizing m with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, pow_zero, Nat.choose_self, Nat.cast_one,
      Nat.cast_zero, add_zero, Nat.factorial_zero, mul_one, Nat.factorial_succ]
    push_cast
    field_simp
  | succ b ih =>
    rw [sum_range_succ']
    have hsplit : ∀ k ∈ range (b + 1), (-1 : ℚ) ^ (k + 1) * ((b + 1).choose (k + 1) : ℚ) /
        ((m : ℚ) + ((k + 1 : ℕ) : ℚ) + 1) =
        -((-1 : ℚ) ^ k * (b.choose k : ℚ) / (((m + 1 : ℕ) : ℚ) + k + 1)) +
          (-1 : ℚ) ^ (k + 1) * (b.choose (k + 1) : ℚ) / ((m : ℚ) + ((k + 1 : ℕ) : ℚ) + 1) := by
      intro k _
      rw [Nat.choose_succ_succ]
      push_cast
      ring
    rw [sum_congr rfl hsplit, sum_add_distrib, sum_neg_distrib, ih (m + 1)]
    have e : ∑ k ∈ range (b + 1), (-1 : ℚ) ^ (k + 1) * (b.choose (k + 1) : ℚ) /
        ((m : ℚ) + ((k + 1 : ℕ) : ℚ) + 1) + (-1 : ℚ) ^ 0 * ((b + 1).choose 0 : ℚ) /
          ((m : ℚ) + ((0 : ℕ) : ℚ) + 1) =
        (m.factorial * b.factorial : ℚ) / (m + b + 1).factorial := by
      rw [← ih m, sum_range_succ, sum_range_succ' _ b]
      simp [Nat.choose_succ_self]
    rw [add_assoc, e]
    rw [show m + 1 + b + 1 = m + b + 1 + 1 by ring, show m + (b + 1) + 1 = m + b + 1 + 1 by ring,
      Nat.factorial_succ (m + b + 1), Nat.factorial_succ m, Nat.factorial_succ b]
    push_cast
    field_simp
    ring

/-- The moments as integer combinations of reciprocals of integers `≤ j+a+b+1`:
`ν_j = ∑_k (-1)^{j+k} binom(b,k) / (j+k+a+1)`, i.e. the coefficientwise integral of the
expanded weight. -/
theorem integralWeightMoment_eq_sum (a b j : ℕ) :
    integralWeightMoment a b j =
      ∑ k ∈ range (b + 1), (-1 : ℚ) ^ (j + k) * (b.choose k : ℚ) / ((j + k + a + 1 : ℕ) : ℚ) := by
  rw [integralWeightMoment_eq, mul_div_assoc, ← sum_neg_one_pow_choose_div (j + a) b, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [pow_add]; push_cast; ring

/-- The moments are those of the integral: `ν_j = ∫_{-1}^0 t^j (-t)^a (t+1)^b dt`. -/
theorem integralWeightMoment_eq_integral (a b j : ℕ) :
    ((integralWeightMoment a b j : ℚ) : ℝ) =
      ∫ t in (-1 : ℝ)..0, t ^ j * (-t) ^ a * (t + 1) ^ b := by
  have e : (fun t : ℝ => t ^ j * (-t) ^ a * (t + 1) ^ b) =
      fun t => ∑ k ∈ range (b + 1), ((-1) ^ a * (b.choose k : ℝ)) * t ^ (j + a + k) := by
    funext t
    rw [add_pow, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [neg_pow, one_pow, mul_one]
    ring
  rw [e, intervalIntegral.integral_finsetSum (fun k _ => (by fun_prop :
    Continuous fun t : ℝ => (-1) ^ a * (b.choose k : ℝ) * t ^ (j + a + k)).intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const_mul, integral_pow]
  rw [integralWeightMoment_eq_sum]
  push_cast
  refine sum_congr rfl fun k _ => ?_
  have hsq : ((-1 : ℝ) ^ a) * (-1) ^ a = 1 := by rw [← mul_pow]; simp
  have hpos : (0 : ℝ) < (j : ℝ) + k + a + 1 := by positivity
  rw [zero_pow (by omega), show (j : ℝ) + a + k + 1 = (j : ℝ) + k + a + 1 by ring]
  field_simp
  rw [pow_add, pow_add, pow_add, pow_add]
  linear_combination (-(-1 : ℝ) ^ j * (-1) ^ k * (b.choose k : ℝ)) * hsq

/-! ### The valuation bound (2.9) -/

theorem neg_le_padicValRat_sum {p : ℕ} [Fact p.Prime] {L : ℤ} (hL : 0 ≤ L) {s : Finset ℕ}
    {F : ℕ → ℚ} (h : ∀ i ∈ s, -L ≤ padicValRat p (F i)) :
    -L ≤ padicValRat p (∑ i ∈ s, F i) := by
  induction s using Finset.induction_on with
  | empty => simp; omega
  | insert i s hi ih =>
    rw [sum_insert hi]
    by_cases h0 : F i + ∑ x ∈ s, F x = 0
    · rw [h0, padicValRat.zero]; omega
    · exact le_trans (le_min (h i (mem_insert_self _ _))
        (ih fun j hj => h j (mem_insert_of_mem hj))) (padicValRat.min_le_padicValRat_add h0)

theorem neg_log_le_padicValRat_int_div {p : ℕ} [Fact p.Prime] (z : ℤ) {m N : ℕ} (hm : 1 ≤ m)
    (hmN : m ≤ N) : -(Nat.log p N : ℤ) ≤ padicValRat p ((z : ℚ) / (m : ℚ)) := by
  by_cases hz : z = 0
  · simp [hz]
  rw [padicValRat.div (Int.cast_ne_zero.mpr hz) (Nat.cast_ne_zero.mpr (by omega)),
    padicValRat.of_int, padicValRat.of_nat]
  have h1 := padicValNat_le_nat_log (p := p) m
  have h2 := Nat.log_mono_right (b := p) hmN
  omega

/-- **The moment valuation bound (2.9):** `v_p(I(t^j)) ≥ -⌊log_p(j+a+b+1)⌋`. -/
theorem neg_log_le_padicValRat_integralWeightMoment (p : ℕ) [Fact p.Prime] (a b j : ℕ) :
    -(Nat.log p (j + a + b + 1) : ℤ) ≤ padicValRat p (integralWeightMoment a b j) := by
  rw [integralWeightMoment_eq_sum]
  refine neg_le_padicValRat_sum (by positivity) fun k hk => ?_
  have e : (-1 : ℚ) ^ (j + k) * (b.choose k : ℚ) = (((-1) ^ (j + k) * b.choose k : ℤ) : ℚ) := by
    push_cast; ring
  rw [e]
  exact neg_log_le_padicValRat_int_div _ (by omega) (by simp only [mem_range] at hk; omega)

/-! ### Reflection `t ↦ -t` of the moment functional -/

section Reflection

variable {K : Type*} [CommRing K]

private lemma neg_one_pow_mul_self (j : ℕ) : (-1 : K) ^ j * (-1) ^ j = 1 := by
  rw [← mul_pow]; simp

private lemma monomial_comp_neg_X (j : ℕ) (c : K) :
    (monomial j c).comp (-X) = C (c * (-1) ^ j) * X ^ j := by
  rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, neg_pow, C_mul, C_pow, C_neg,
    C_1]
  ring

theorem momentFunctional_comp_neg_X (μ : ℕ → K) (κ : K) (p : K[X]) :
    momentFunctional (fun j => (-1) ^ j * κ * μ j) (p.comp (-X)) =
      κ * momentFunctional μ p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp, map_add, hp, hq, map_add, mul_add]
  | monomial j c =>
    rw [monomial_comp_neg_X, momentFunctional_C_mul, momentFunctional_X_pow,
      momentFunctional_monomial]
    linear_combination (c * κ * μ j) * neg_one_pow_mul_self (K := K) j

theorem momentQuotient_comp_neg_X (μ : ℕ → K) (κ : K) (p : K[X]) :
    momentQuotient (fun j => (-1) ^ j * κ * μ j) (p.comp (-X)) =
      C (-κ) * (momentQuotient μ p).comp (-X) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp, map_add, hp, hq, map_add, add_comp, mul_add]
  | monomial j c =>
    rw [monomial_comp_neg_X, ← monomial_one_right_eq_X_pow, momentQuotient_C_mul,
      momentQuotient_monomial, momentQuotient_monomial, C_1, one_mul, mul_comp, C_comp,
      momentKernel_eq, momentKernel_eq, Polynomial.sum_comp, mul_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    obtain ⟨d, rfl⟩ : ∃ d, j = k + 1 + d := ⟨j - 1 - k, by simp only [mem_range] at hk; omega⟩
    rw [show k + 1 + d - 1 - k = d by omega, mul_comp, C_comp, X_pow_comp, neg_pow]
    simp only [C_mul, C_pow, C_neg, C_1]
    have h := neg_one_pow_mul_self (K := K[X]) d
    rw [pow_add, pow_add, pow_one]
    linear_combination (-(C c * C κ * C (μ d) * (-1) ^ k * X ^ k)) * h

end Reflection

/-! ### The data `Q`, `V`, `𝒞_n` and the comparison with Lemma 2.1 -/

/-- `Q = P_n^{(a,b)}(2X+1) / binom(n+a, a)`, normalized by `Q(0) = 1`. -/
noncomputable def integralWeightQ (a b n : ℕ) : ℚ[X] :=
  C (1 / ((n + a).choose a : ℚ)) * (jacobiP a b n).comp (2 * X + 1)

theorem integralWeightQ_eq (a b n : ℕ) : integralWeightQ a b n =
    C (1 / ((n + a).choose a : ℚ)) * (jacobiP a b n).comp (2 * X + 1) := (rfl)

/-- `V(X) = I_t((Q(X) - Q(t))/(X - t))`. -/
noncomputable def integralWeightV (a b n : ℕ) : ℚ[X] :=
  momentQuotient (integralWeightMoment a b) (integralWeightQ a b n)

theorem integralWeightV_eq (a b n : ℕ) :
    integralWeightV a b n = momentQuotient (integralWeightMoment a b) (integralWeightQ a b n) :=
  (rfl)

/-- The root constant `𝒞_n = -(a!)² n! (n+b)! / ((n+a)! (n+a+b)!)`. -/
noncomputable def integralWeightConstant (a b n : ℕ) : ℚ :=
  -((a.factorial : ℚ) ^ 2 * n.factorial * (n + b).factorial) /
    ((n + a).factorial * (n + a + b).factorial)

theorem integralWeightConstant_eq (a b n : ℕ) : integralWeightConstant a b n =
    -((a.factorial : ℚ) ^ 2 * n.factorial * (n + b).factorial) /
      ((n + a).factorial * (n + a + b).factorial) := (rfl)

theorem ascPochhammer_eval_natCast_add_one (m j : ℕ) :
    (ascPochhammer ℚ j).eval ((m : ℚ) + 1) * m.factorial = (m + j).factorial := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ascPochhammer_succ_eval, show m + (j + 1) = (m + j) + 1 by ring, Nat.factorial_succ]
    push_cast
    linear_combination ((m : ℚ) + 1 + j) * ih

/-- The Beta value `B(a+1, b+1) = a! b! / (a+b+1)!`. -/
noncomputable def integralWeightBeta (a b : ℕ) : ℚ :=
  (a.factorial * b.factorial : ℚ) / (a + b + 1).factorial

/-- The present functional is `B(a+1,b+1)` times the reflected Jacobi probability functional:
`ν_j = (-1)^j B(a+1,b+1) μ_j`. -/
theorem integralWeightMoment_eq_jacobiMoment (a b j : ℕ) :
    integralWeightMoment a b j = (-1) ^ j * integralWeightBeta a b * jacobiMoment a b j := by
  have h1 := ascPochhammer_eval_natCast_add_one a j
  have h2 := ascPochhammer_eval_natCast_add_one (a + b + 1) j
  rw [show ((a + b + 1 : ℕ) : ℚ) + 1 = (a : ℚ) + b + 2 by push_cast; ring] at h2
  have hp1 : (ascPochhammer ℚ j).eval ((a : ℚ) + 1) = (a + j).factorial / a.factorial :=
    eq_div_of_mul_eq (by positivity) h1
  have hp2 : (ascPochhammer ℚ j).eval ((a : ℚ) + b + 2) =
      (a + b + 1 + j).factorial / (a + b + 1).factorial :=
    eq_div_of_mul_eq (by positivity) h2
  rw [integralWeightMoment_eq, integralWeightBeta, jacobiMoment_eq, hp1, hp2,
    show j + a = a + j by ring, show a + j + b + 1 = a + b + 1 + j by ring]
  have : (0 : ℚ) < (a + b + 1 + j).factorial := by positivity
  field_simp

theorem integralWeightQ_eq_comp (a b n : ℕ) :
    integralWeightQ a b n =
      C (1 / ((n + a).choose a : ℚ)) * (jacobiShifted a b n).comp (-X) := by
  rw [integralWeightQ_eq, jacobiShifted_eq, comp_assoc]
  congr 2
  simp only [sub_comp, one_comp, mul_comp, X_comp]
  rw [show (2 : ℚ[X]).comp (-X) = 2 from by simp]
  ring

theorem integralWeightV_eq_comp (a b n : ℕ) :
    integralWeightV a b n =
      C (-integralWeightBeta a b / ((n + a).choose a : ℚ)) *
        (jacobiSecondPoly a b n).comp (-X) := by
  rw [integralWeightV_eq, integralWeightQ_eq_comp, momentQuotient_C_mul,
    show integralWeightMoment a b = fun j => (-1) ^ j * integralWeightBeta a b * jacobiMoment a b j
      from funext (integralWeightMoment_eq_jacobiMoment a b), momentQuotient_comp_neg_X,
    jacobiSecondPoly_eq]
  simp only [div_eq_mul_inv, one_mul, map_neg, map_mul]
  ring

/-- Orthogonality: `I(t^j Q) = 0` for `j < n`. -/
theorem integralWeightFunctional_X_pow_mul_Q (a b : ℕ) {n j : ℕ} (hj : j < n) :
    integralWeightFunctional a b (X ^ j * integralWeightQ a b n) = 0 := by
  have hα : (-1 : ℚ) < a := by have := (Nat.cast_nonneg a : (0 : ℚ) ≤ a); linarith
  have hβ : (-1 : ℚ) < b := by have := (Nat.cast_nonneg b : (0 : ℚ) ≤ b); linarith
  have e : X ^ j * integralWeightQ a b n = C (1 / ((n + a).choose a : ℚ)) *
      (C ((-1) ^ j) * (jacobiShifted a b n * X ^ j)).comp (-X) := by
    have hX : (-X : ℚ[X]) ^ j = C ((-1) ^ j) * X ^ j := by rw [neg_pow, C_pow, C_neg, C_1]
    rw [integralWeightQ_eq_comp, mul_comp, mul_comp, C_comp, X_pow_comp, hX]
    have h : (C ((-1 : ℚ) ^ j)) * C ((-1) ^ j) = 1 := by
      rw [← C_mul, ← mul_pow]; simp
    linear_combination (-(C (1 / ((n + a).choose a : ℚ)) * (jacobiShifted a b n).comp (-X) *
      X ^ j)) * h
  rw [e, integralWeightFunctional_eq, momentFunctional_C_mul,
    show integralWeightMoment a b = fun j => (-1) ^ j * integralWeightBeta a b * jacobiMoment a b j
      from funext (integralWeightMoment_eq_jacobiMoment a b), momentFunctional_comp_neg_X,
    momentFunctional_C_mul, ← jacobiFunctional_eq,
    jacobiFunctional_jacobiShifted_mul_X_pow n hα hβ j hj]
  simp

/-- The constant: `𝒞_n = -B(a+1,b+1) C_n / binom(n+a,a)²`. -/
theorem integralWeightConstant_eq_jacobi (a b : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    integralWeightConstant a b n =
      -(integralWeightBeta a b / ((n + a).choose a : ℚ) ^ 2) * jacobiWronskianConstant a b n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := ascPochhammer_eval_natCast_add_one a (m + 1)
  have h2 := ascPochhammer_eval_natCast_add_one b (m + 1)
  have h3 := ascPochhammer_eval_natCast_add_one (a + b + 1) m
  rw [show ((a + b + 1 : ℕ) : ℚ) + 1 = (a : ℚ) + b + 2 by push_cast; ring] at h3
  have hB := Nat.choose_mul_factorial_mul_factorial (n := m + 1 + a) (k := a) (by omega)
  rw [show m + 1 + a - a = m + 1 by omega] at hB
  have hBq : ((m + 1 + a).choose a : ℚ) * (a.factorial * (m + 1).factorial) =
      (m + 1 + a).factorial := by rw [← mul_assoc]; exact_mod_cast hB
  rw [integralWeightConstant_eq, integralWeightBeta, jacobiWronskianConstant_eq,
    add_tsub_cancel_right,
    eq_div_of_mul_eq (by positivity) h1, eq_div_of_mul_eq (by positivity) h2,
    eq_div_of_mul_eq (by positivity) h3,
    eq_div_of_mul_eq (by positivity) hBq,
    show a + (m + 1) = m + 1 + a by ring, show b + (m + 1) = m + 1 + b by ring,
    show a + b + 1 + m = m + 1 + a + b by ring]
  have : (0 : ℚ) < (m + 1 + a + b).factorial := by positivity
  have : (0 : ℚ) < (m + 1 + a).factorial := by positivity
  field_simp

/-- **Lemma 2.3 (2.10).** For integers `a, b ≥ 0` and `n ≥ 1`, at every root `z` of `Q` in any
field of characteristic zero, `p₀(z) Q'(z) V(z) = 𝒞_n` with `p₀ = X(X+1)` and
`𝒞_n = -(a!)² n! (n+b)! / ((n+a)! (n+a+b)!)`. -/
theorem integralWeight_root_identity (a b : ℕ) {n : ℕ} (hn : 1 ≤ n) {K : Type*} [Field K]
    [CharZero K] {z : K} (hz : aeval z (integralWeightQ a b n) = 0) :
    z * (z + 1) * aeval z (derivative (integralWeightQ a b n)) *
        aeval z (integralWeightV a b n) = (integralWeightConstant a b n : K) := by
  have hα : (-1 : ℚ) < a := by have := (Nat.cast_nonneg a : (0 : ℚ) ≤ a); linarith
  have hβ : (-1 : ℚ) < b := by have := (Nat.cast_nonneg b : (0 : ℚ) ≤ b); linarith
  set B : ℚ := ((n + a).choose a : ℚ) with hBdef
  have hB : B ≠ 0 := by
    rw [hBdef]; exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hBK : (B : K) ≠ 0 := by exact_mod_cast hB
  rw [integralWeightQ_eq_comp] at hz ⊢
  rw [integralWeightV_eq_comp, integralWeightConstant_eq_jacobi a b hn]
  simp only [map_mul, aeval_C, aeval_comp, aeval_X, map_neg, derivative_mul, derivative_C,
    zero_mul, zero_add, derivative_comp, derivative_X, eq_ratCast] at hz ⊢
  have hys : aeval (-z) (jacobiShifted a b n) = 0 := by
    rcases mul_eq_zero.mp hz with h | h
    · simp only [one_div, Rat.cast_inv, Rat.cast_natCast, inv_eq_zero, Nat.cast_eq_zero] at h
      exact absurd h (Nat.choose_pos (by omega)).ne'
    · exact h
  have hW := congrArg (aeval (-z)) (jacobi_wronskian_source hα hβ hn)
  simp only [map_add, map_mul, map_sub, map_pow, aeval_C, aeval_X, map_one, hys, eq_ratCast]
    at hW
  simp only [map_one, neg_mul, one_mul]
  push_cast
  have hBK' : ((n + a).choose a : K) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  field_simp
  linear_combination (-(integralWeightBeta a b : K)) * hW

end ArithmeticOfJacobiPolynomials
