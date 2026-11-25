/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.SymmetricCriterion
public import ArithmeticOfJacobiPolynomials.Analysis.SymmetricResultantBounds

/-!
# Irreducibility for symmetric parameters (Theorem 1.4, explicit range; Theorem 1.5, `m ≥ 200`)

* `ArithmeticOfJacobiPolynomials.irreducible_reducedGegenbauer_of_elementary_criterion`: Theorem
3.4, second
  assertion: for `m ≥ max{2r, 4}` and `M = m + r ≥ 9`, the elementary criterion (3.14)
  implies that `F_{m,r,δ} = C_{2m+δ}^{r+1/2}/x^δ` is irreducible.
* `ArithmeticOfJacobiPolynomials.irreducible_reducedGegenbauer_of_explicit_range`: the first
assertion of
  Theorem 1.4, `F_{m,r,δ}` is irreducible for `m ≥ max{100r, 1000}`.
* `ArithmeticOfJacobiPolynomials.irreducible_derivative_legendreP_of_two_hundred_le`: the
first-derivative part
  of the proof of Theorem 1.5 for `m ≥ 200`: `P'_{2m+1+δ}/x^δ` is irreducible.

All are conditional on the cited `HansonLcmBound` ([Hanson, Theorem 1]),
`JacobiSimpleRealZeros`
([DLMF, §18.2(vi)]).
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset Real

/-- The prime-power sum `Ψ_m(S)` in the explicit form used by the arithmetic lemmas. -/
theorem primePowerLogSum_natCast_eq (m S : ℕ) : primePowerLogSum m (S : ℝ) =
    ∑ p ∈ (range (m + 1)).filter Nat.Prime, ((Nat.log p S : ℕ) : ℝ) * log p := by
  rw [primePowerLogSum_eq]
  exact sum_congr rfl fun p _ => by rw [floor_logb_natCast_eq]

/-- **Theorem 3.4, elementary criterion (3.14).** For `m ≥ max{2r, 4}`
with `M = m + r ≥ 9`, `n = 2m+δ`, `S = 2n+2r+1`, `K = binom(m+r, r)`, `B = binom(n+r, r)`: if
`m log 4 > (M + √S) log 3 + log(8√m) + log K + 2 log B - log binom(2r, r)`, then
`F_{m,r,δ}` is irreducible over `ℚ`. -/
theorem irreducible_reducedGegenbauer_of_elementary_criterion (hH : HansonLcmBound)
     (hZ : JacobiSimpleRealZeros) {m r δ : ℕ} (hδ : δ ≤ 1)
    (hm : max (2 * r) 4 ≤ m) (hM : 9 ≤ m + r)
    (h : ((m : ℝ) + r + √((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ)) * log 3 +
        log (8 * √(m : ℝ)) + log ((m + r).choose r : ℝ) +
        2 * log ((2 * m + δ + r).choose r : ℝ) - log ((2 * r).choose r : ℝ) < m * log 4) :
    Irreducible (reducedGegenbauer m r δ) := by
  obtain ⟨hr2, hm4⟩ : 2 * r ≤ m ∧ 4 ≤ m := ⟨le_of_max_le_left hm, le_of_max_le_right hm⟩
  have hcrit := symmetric_exact_of_elementary hH r m δ hδ hr2 hm4 hM h
  refine irreducible_reducedGegenbauer_of_exact_criterion hZ hδ hm ?_
  rw [primePowerLogSum_natCast_eq, log_primeTruncation]
  linarith

/-- **Theorem 1.4, first assertion.** For integers `r ≥ 0`, `m ≥ max{100r, 1000}` and
`δ ∈ {0,1}`, `F_{m,r,δ} = C_{2m+δ}^{r+1/2}(x)/x^δ` is irreducible over `ℚ`. -/
theorem irreducible_reducedGegenbauer_of_explicit_range (hH : HansonLcmBound)
     (hZ : JacobiSimpleRealZeros) {m r δ : ℕ} (hδ : δ ≤ 1)
    (hm : max (100 * r) 1000 ≤ m) :
    Irreducible (reducedGegenbauer m r δ) := by
  obtain ⟨hr, h1000⟩ : 100 * r ≤ m ∧ 1000 ≤ m :=
    ⟨le_of_max_le_left hm, le_of_max_le_right hm⟩
  exact irreducible_reducedGegenbauer_of_elementary_criterion hH hZ hδ
    (max_le (by omega) (by omega)) (by omega) (symmetric_elementary_of_range r m δ hδ hr h1000)

/-- **First derivatives of Legendre polynomials, `m ≥ 200`** (proof of Theorem 1.5). For
`m ≥ 200` and `δ ∈ {0,1}`, `P'_{2m+δ+1}(x)/x^δ` is irreducible over `ℚ`. -/
theorem irreducible_derivative_legendreP_of_two_hundred_le (hH : HansonLcmBound)
     (hZ : JacobiSimpleRealZeros) {m δ : ℕ} (hδ : δ ≤ 1)
    (hm : 200 ≤ m) :
    Irreducible (derivative (legendreP (2 * m + δ + 1)) /ₘ polyX ^ δ) := by
  have hcrit := first_derivative_exact_criterion_sum hH m δ hδ hm
  rw [← log_primeTruncation] at hcrit
  have := irreducible_reducedDerivative_of_exact_criterion hZ (r := 1) hδ
    (max_le (by omega) (by omega)) hcrit
  simpa using this

/-- **Legendre polynomials, `m ≥ 100`, directly from the comparison** (proof of Theorem 1.5,
`r = 0`). For `r = 0` one has `K = A = 1`, and the exact criterion of Theorem 3.4 together with
`m log(4/3) > √(4m+3) log 3 + log(8√m)` (`m ≥ 100`) and Hanson's bound gives irreducibility of
`F_{m,0,δ} = P_{2m+δ}/x^δ`. -/
theorem irreducible_reducedGegenbauer_zero_of_hundred_le (hH : HansonLcmBound)
    (hZ : JacobiSimpleRealZeros) {m δ : ℕ} (hδ : δ ≤ 1) (hm : 100 ≤ m) :
    Irreducible (reducedGegenbauer m 0 δ) := by
  have hcrit := legendre_exact_criterion hH m δ hδ hm
  have hA : symmetricRatio (2 * m + δ) 0 = 1 := by
    rw [symmetricRatio_eq]
    simp only [mul_zero, add_zero]
    have h : ((2 * m + δ).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    rw [sq, div_self (mul_ne_zero h h)]
  have hpt : log (primeTruncation 1 m) = 0 := by
    rw [log_primeTruncation]
    simp
  refine irreducible_reducedGegenbauer_of_exact_criterion hZ hδ
    (max_le (by omega) (by omega)) ?_
  rw [hA, hpt]
  simpa using hcrit

end ArithmeticOfJacobiPolynomials
