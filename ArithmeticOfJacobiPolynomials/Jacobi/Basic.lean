/- Assembled by AxiomProver. -/
module

public import Mathlib.RingTheory.Binomial
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Jacobi, Legendre and Gegenbauer polynomials

The Jacobi polynomial `P_n^{(α,β)}` with rational parameters, in the normalization (1.1) of
the manuscript:
`P_n^{(α,β)}(x) = 2^{-n} ∑_{j=0}^n binom(n+α, n-j) binom(n+β, j) (x-1)^j (x+1)^{n-j}`,
where `binom(z, j) = z(z-1)⋯(z-j+1)/j!` is the generalized binomial coefficient
(`Ring.choose`). See [DLMF, 18.5.8].
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-- The Jacobi polynomial `P_n^{(α,β)} ∈ ℚ[X]` in the normalization (1.1) of the manuscript
([DLMF, 18.5.8]). It is defined for all rational parameters, including those outside the
orthogonality range `α, β > -1`. -/
noncomputable def jacobiP (α β : ℚ) (n : ℕ) : ℚ[X] :=
  C ((1 / 2 : ℚ) ^ n) * ∑ j ∈ Finset.range (n + 1),
    C (Ring.choose ((n : ℚ) + α) (n - j) * Ring.choose ((n : ℚ) + β) j) *
      (X - 1) ^ j * (X + 1) ^ (n - j)

theorem jacobiP_eq (α β : ℚ) (n : ℕ) : jacobiP α β n =
    C ((1 / 2 : ℚ) ^ n) * ∑ j ∈ Finset.range (n + 1),
      C (Ring.choose ((n : ℚ) + α) (n - j) * Ring.choose ((n : ℚ) + β) j) *
        (X - 1) ^ j * (X + 1) ^ (n - j) := (rfl)

/-- The Legendre polynomial `P_n = P_n^{(0,0)}`. -/
noncomputable def legendreP (n : ℕ) : ℚ[X] := jacobiP 0 0 n

theorem legendreP_eq (n : ℕ) : legendreP n = jacobiP 0 0 n := (rfl)

/-- The Gegenbauer (ultraspherical) polynomial `C_n^{ν}`, given by the explicit formula
`C_n^{ν}(x) = ∑_{k=0}^{⌊n/2⌋} (-1)^k (ν)_{n-k} / (k! (n-2k)!) (2x)^{n-2k}` of [DLMF, 18.5.10].
That it is the coefficient of `t^n` in `(1 - 2xt + t^2)^{-ν}` ([DLMF, 18.12.4]), which is the
definition used in the manuscript, is proved in `gegenbauerC_generatingFunction`. -/
noncomputable def gegenbauerC (ν : ℚ) (n : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    C ((-1) ^ k * (ascPochhammer ℚ (n - k)).eval ν /
        ((k.factorial : ℚ) * ((n - 2 * k).factorial : ℚ)) * 2 ^ (n - 2 * k)) * X ^ (n - 2 * k)

theorem gegenbauerC_eq (ν : ℚ) (n : ℕ) : gegenbauerC ν n =
    ∑ k ∈ Finset.range (n / 2 + 1),
      C ((-1) ^ k * (ascPochhammer ℚ (n - k)).eval ν /
        ((k.factorial : ℚ) * ((n - 2 * k).factorial : ℚ)) * 2 ^ (n - 2 * k)) * X ^ (n - 2 * k) :=
  (rfl)

/-- The reduced Gegenbauer polynomial `F_{m,r,δ} = C_{2m+δ}^{r+1/2} / x^δ` of (1.4); in the
manuscript `δ ∈ {0,1}`, and division by `x` is exact for odd degree. -/
noncomputable def reducedGegenbauer (m r δ : ℕ) : ℚ[X] :=
  gegenbauerC ((r : ℚ) + 1 / 2) (2 * m + δ) /ₘ X ^ δ

theorem reducedGegenbauer_eq (m r δ : ℕ) :
    reducedGegenbauer m r δ = gegenbauerC ((r : ℚ) + 1 / 2) (2 * m + δ) /ₘ X ^ δ := (rfl)

/-- The reduced Legendre polynomial `L_{2m+δ} = P_{2m+δ} / x^δ`, for `δ ∈ {0,1}`. -/
noncomputable def reducedLegendre (m δ : ℕ) : ℚ[X] :=
  legendreP (2 * m + δ) /ₘ X ^ δ

theorem reducedLegendre_eq (m δ : ℕ) :
    reducedLegendre m δ = legendreP (2 * m + δ) /ₘ X ^ δ := (rfl)

end ArithmeticOfJacobiPolynomials
