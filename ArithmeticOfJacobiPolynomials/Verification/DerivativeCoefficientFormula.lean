module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Rat.Defs

/-! # The factorial coefficient in Appendix C -/

public section

namespace ArithmeticOfJacobiPolynomials.DerivativeModel

/-- The coefficient of the term indexed by `k` in Appendix C. -/
@[expose] def termCoeff (m δ k : ℕ) : ℚ :=
  (-1) ^ k * ((2 * (2 * m + δ) + 2 - 2 * k).factorial : ℚ) /
    ((k.factorial : ℚ) * ((2 * m + δ + 1 - k).factorial : ℚ) *
      ((2 * m + δ - 2 * k).factorial : ℚ))

/-- In power `i`, the factorial formula has at most one contributing index. -/
@[expose] def targetCoeff (m δ i : ℕ) : ℚ :=
  if i ≤ 2 * m ∧ i % 2 = 0 then termCoeff m δ (m - i / 2) else 0

end ArithmeticOfJacobiPolynomials.DerivativeModel
