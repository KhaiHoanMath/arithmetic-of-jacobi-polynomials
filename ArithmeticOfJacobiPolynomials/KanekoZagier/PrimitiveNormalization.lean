/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.MomentFunctional
public import Mathlib.RingTheory.Polynomial.Content

/-!
# The primitive normalization of the Kaneko–Zagier Jacobi polynomials (eq. (4.1))

For `λ, μ ∈ {-1, 1}`, `α = λ/3`, `β = μ/2` and `y_n(t) = P_n^{(α,β)}(1-2t)`
(`jacobiShifted α β n`), the manuscript puts
`κ_n = 2^{n + v_2(n!)} 3^{n + v_3(n!)}`, `g_n = cont(κ_n y_n)` and `H_n = (κ_n / g_n) y_n`
(§4.1).

* `kzKappa n` is `κ_n`;
* `kzScaled l μ n ∈ ℤ[X]` is `κ_n y_n` (its coefficients are the numerators of the rational
  coefficients `κ_n [t^j] y_n`; that these are integers, i.e. that `kzScaled` maps to
  `κ_n y_n`, is part of Lemma 4.1);
* `kzContent l μ n = g_n` (a natural number) and `kzPrimitive l μ n = H_n`, the primitive
  part of `kzScaled l μ n`.

Here `l` stands for `λ`. The definitions make sense for all integers `l, μ`; the results
of Section 4 assume `l, μ ∈ {-1, 1}`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-- `κ_n = 2^{n + v_2(n!)} 3^{n + v_3(n!)}` of (4.1). -/
def kzKappa (n : ℕ) : ℕ := 2 ^ (n + padicValNat 2 n.factorial) * 3 ^ (n + padicValNat 3 n.factorial)

theorem kzKappa_eq (n : ℕ) :
    kzKappa n = 2 ^ (n + padicValNat 2 n.factorial) * 3 ^ (n + padicValNat 3 n.factorial) :=
  (rfl)

/-- The integer polynomial `κ_n y_n`, `y_n(t) = P_n^{(λ/3, μ/2)}(1-2t)`: the coefficient of
`t^j` is the numerator of `κ_n [t^j] y_n` (an integer, by Lemma 4.1). -/
noncomputable def kzScaled (l μ : ℤ) (n : ℕ) : ℤ[X] :=
  ∑ j ∈ range (n + 1),
    C (((kzKappa n : ℚ) * (jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n).coeff j).num) * X ^ j

theorem kzScaled_eq (l μ : ℤ) (n : ℕ) : kzScaled l μ n = ∑ j ∈ range (n + 1),
    C (((kzKappa n : ℚ) * (jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n).coeff j).num) * X ^ j :=
  (rfl)

/-- `g_n = cont(κ_n y_n)`, the positive gcd of the coefficients of `κ_n y_n`. -/
noncomputable def kzContent (l μ : ℤ) (n : ℕ) : ℕ := (kzScaled l μ n).content.natAbs

theorem kzContent_eq (l μ : ℤ) (n : ℕ) : kzContent l μ n = (kzScaled l μ n).content.natAbs :=
  (rfl)

/-- `H_n = (κ_n / g_n) y_n`, the primitive part of `κ_n y_n`. -/
noncomputable def kzPrimitive (l μ : ℤ) (n : ℕ) : ℤ[X] := (kzScaled l μ n).primPart

theorem kzPrimitive_eq (l μ : ℤ) (n : ℕ) : kzPrimitive l μ n = (kzScaled l μ n).primPart :=
  (rfl)

end ArithmeticOfJacobiPolynomials
