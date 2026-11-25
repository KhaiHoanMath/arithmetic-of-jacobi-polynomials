/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Remarks.Modular

/-!
# The Hasse polynomial of the Legendre family (§6.4)

For `p = 2m + 1`, the Hasse invariant of `y² = x(x-1)(x-z)` is the coefficient of `x^{p-1}` in
`(x(x-1)(x-z))^m`. We prove that this coefficient is `(-1)^m ∑_j binom(m,j)² z^j`, which by
`one_sub_pow_mul_legendreP_eval` (Remarks/Modular) is `(-1)^m (1-z)^m P_m((1+z)/(1-z))`. This is
the arithmetic content of the manuscript's remark; that the Hasse invariant vanishes exactly at
the supersingular Legendre curves follows conditionally from the general Hasse–Deuring
criterion in `External.lean` (KZ, §2, Proposition 1 and Corollary). The torsion-based
supersingularity predicate and this application are in `Remarks.LegendreElliptic`.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-- **The Hasse coefficient of the Legendre family.** Over any commutative ring, the coefficient
of `x^{2m}` in `(x(x-1)(x-z))^m` is `(-1)^m ∑_{j ≤ m} binom(m,j)² z^j`. -/
theorem coeff_legendreCurve_pow {R : Type*} [CommRing R] (m : ℕ) (z : R) :
    ((polyX * (polyX - 1) * (polyX - C z)) ^ m).coeff (2 * m) =
      (-1) ^ m * ∑ j ∈ range (m + 1), ((m.choose j : ℕ) : R) ^ 2 * z ^ j := by
  have e : (polyX * (polyX - 1) * (polyX - C z)) ^ m = polyX ^ m * ((polyX + C (-1)) ^ m *
    (polyX + C (-z)) ^ m) := by
    rw [mul_assoc, mul_pow, mul_pow, C_neg, C_neg, C_1, ← sub_eq_add_neg, ← sub_eq_add_neg]
  rw [e, show 2 * m = m + m by ring, coeff_X_pow_mul, coeff_mul,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  dsimp only
  have hi : i ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [coeff_X_add_C_pow, coeff_X_add_C_pow, Nat.sub_sub_self hi, Nat.choose_symm hi]
  have h1 : ((-1 : R)) ^ (m - i) * (-z) ^ i = (-1) ^ m * z ^ i := by
    rw [neg_pow z, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hi]
  linear_combination ((m.choose i : ℕ) : R) ^ 2 * h1

/-- With `one_sub_pow_mul_legendreP_eval`: for `p = 2m + 1` the Hasse coefficient equals
`(-1)^m ∑ binom(m,j)² z^j`, the transformed Legendre polynomial of §6.4. -/
theorem coeff_legendreCurve_pow_two_mul_add_one {R : Type*} [CommRing R] (m : ℕ) (z : R) :
    ((polyX * (polyX - 1) * (polyX - C z)) ^ ((2 * m + 1 - 1) / 2)).coeff (2 * m + 1 - 1) =
      (-1) ^ m * ∑ j ∈ range (m + 1), ((m.choose j : ℕ) : R) ^ 2 * z ^ j := by
  rw [show (2 * m + 1 - 1) / 2 = m by omega, show 2 * m + 1 - 1 = 2 * m by omega]
  exact coeff_legendreCurve_pow m z

end ArithmeticOfJacobiPolynomials
