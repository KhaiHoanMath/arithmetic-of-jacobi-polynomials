/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Jacobi polynomials over characteristic-zero fields

The polynomial formula is defined for arbitrary parameters in a characteristic-zero field.
This permits literature statements to quantify over real or complex parameters, with their
rational-parameter instances obtained by coefficient transport.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

variable {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L]

/-- The Jacobi polynomial in the normalization of DLMF (18.5.8), with arbitrary parameters. -/
noncomputable def jacobiPolynomial (α β : K) (n : ℕ) : K[X] :=
  C ((1 / 2 : K) ^ n) * ∑ j ∈ Finset.range (n + 1),
    C (Ring.choose ((n : K) + α) (n - j) * Ring.choose ((n : K) + β) j) *
      (X - 1) ^ j * (X + 1) ^ (n - j)

/-- The finite-binomial formula (1.1), exposed for comparison with other coefficient APIs. -/
theorem jacobiPolynomial_eq (α β : K) (n : ℕ) :
    jacobiPolynomial α β n =
      C ((1 / 2 : K) ^ n) * ∑ j ∈ Finset.range (n + 1),
        C (Ring.choose ((n : K) + α) (n - j) * Ring.choose ((n : K) + β) j) *
          (X - 1) ^ j * (X + 1) ^ (n - j) := by
  unfold jacobiPolynomial
  rfl

/-- Coefficient transport preserves the Jacobi polynomial and transports its parameters. -/
theorem map_jacobiPolynomial (φ : K →+* L) (α β : K) (n : ℕ) :
    (jacobiPolynomial α β n).map φ = jacobiPolynomial (φ α) (φ β) n := by
  simp only [jacobiPolynomial, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_sum,
    Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_X,
    Polynomial.map_one, Ring.map_choose φ, map_mul, map_pow, map_div₀, map_one, map_ofNat,
    map_add, map_natCast]

/-- The manuscript's rational Jacobi polynomial is the rational instance of the same formula. -/
theorem jacobiPolynomial_rat (α β : ℚ) (n : ℕ) :
    jacobiPolynomial α β n = jacobiP α β n := by
  rw [jacobiP_eq]
  rfl

/-- The polynomial used in real-root statements is the real instance of the Jacobi formula. -/
theorem map_jacobiP_real (α β : ℚ) (n : ℕ) :
    (jacobiP α β n).map (algebraMap ℚ ℝ) = jacobiPolynomial (α : ℝ) (β : ℝ) n := by
  rw [← jacobiPolynomial_rat, map_jacobiPolynomial]
  rfl

/-- The Gegenbauer polynomial of DLMF (18.5.10), with an arbitrary parameter. -/
noncomputable def gegenbauerPolynomial (ν : K) (n : ℕ) : K[X] :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    C ((-1) ^ k * (ascPochhammer K (n - k)).eval ν /
        ((k.factorial : K) * ((n - 2 * k).factorial : K)) * 2 ^ (n - 2 * k)) * X ^ (n - 2 * k)

/-- Coefficient transport preserves the Gegenbauer polynomial. -/
theorem map_gegenbauerPolynomial (φ : K →+* L) (ν : K) (n : ℕ) :
    (gegenbauerPolynomial ν n).map φ = gegenbauerPolynomial (φ ν) n := by
  simp only [gegenbauerPolynomial, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_ofNat, map_mul, map_div₀, map_pow,
    map_neg, map_one,
    map_ofNat, map_natCast, ← Polynomial.eval_map_apply, ascPochhammer_map]

/-- The rational polynomial used in the manuscript has the same normalization. -/
theorem gegenbauerPolynomial_rat (ν : ℚ) (n : ℕ) :
    gegenbauerPolynomial ν n = gegenbauerC ν n := by
  rw [gegenbauerC_eq]
  rfl

end ArithmeticOfJacobiPolynomials
