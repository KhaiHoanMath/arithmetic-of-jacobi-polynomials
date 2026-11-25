/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.Gegenbauer
public import ArithmeticOfJacobiPolynomials.Jacobi.LegendreDerivatives
public import ArithmeticOfJacobiPolynomials.Galois.LegendreGaloisAll
public import Mathlib.Algebra.Polynomial.Expand

/-!
# The derivative orders `r = 0` and `r = 1` in every degree

The manuscript remarks after Theorem 1.4 that "for derivative orders `r = 0` and `r = 1`, the
conclusion holds without any restriction on `m`", after Corollary 1.7 that "for `r = 0` and
`E = ℚ`, Theorem 1.2 gives every degree. For `r = 1`, irreducibility holds in every degree",
and in §6.6 that "the cases `r = 0, 1` have no exceptions". These are consequences of
Theorem 1.5 (with [Deng, Theorem 1.1] for `r = 0`) and of Theorem 1.2, through
`F_{m,0,δ} = L_{2m+δ}` and `F_{m,1,δ} = P'_{2m+δ+1}/x^δ` (eq. (1.3) with `(2r-1)!! = 1`).

* `reducedGegenbauer_zero_eq`, `reducedGegenbauer_one_eq`: the two identifications;
* `irreducible_reducedGegenbauer_of_le_one`: `F_{m,r,δ}` is irreducible for `r ≤ 1`, `m ≥ 1`;
* `reducedGegenbauer_eq_expand`, `irreducible_reducedGegenbauerSquare_of_irreducible`: `F_{m,r,δ}`
  is even, `F_{m,r,δ}(x) = Q_{m,r,δ}(x²)` (proved from the explicit formula, without the cited
  quadratic transformation), so `Q_{m,r,δ}` is irreducible whenever `F_{m,r,δ}` is;
* `irreducible_reducedGegenbauerSquare_of_le_one`: `Q_{m,r,δ}` is irreducible for `r ≤ 1`,
  `m ≥ 1`;
* `galoisGroupIsWreath_reducedGegenbauer_zero`: `Gal(F_{m,0,δ}/ℚ) = W_m` for every `m ≥ 1`.

The cited inputs are hypotheses: `DengLegendreIrreducibility` ([Deng, Theorem 1.1]) and the
literature used by Theorems 1.2 and 1.5 (`HansonLcmBound`,
`JacobiSimpleRealZeros`, `BMORPrimeCountingBound`, `BrunTitchmarshInequality`,
`JonesCycleTheorem`, `CullinanHajirLegendreGalois`, `PrimesModFourInDyadicInterval`)
and the manuscript computer inputs `FirstDerivativeIntegerInequalities` and
`FirstDerivativeFactorDegreeChecks` (Lemma C.2).
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-- `F_{m,0,δ} = C_{2m+δ}^{1/2}/x^δ = P_{2m+δ}/x^δ = L_{2m+δ}`. -/
theorem reducedGegenbauer_zero_eq (m δ : ℕ) : reducedGegenbauer m 0 δ = reducedLegendre m δ := by
  have h := iterate_derivative_legendreP_eq_gegenbauerC (2 * m + δ) 0
  have hd : (2 * 0 - 1).doubleFactorial = 1 := by norm_num [Nat.doubleFactorial]
  rw [hd, Nat.cast_one, map_one, one_mul, Function.iterate_zero_apply, add_zero] at h
  rw [reducedGegenbauer_eq, reducedLegendre_eq, ← h]

/-- `F_{m,1,δ} = C_{2m+δ}^{3/2}/x^δ = P'_{2m+δ+1}/x^δ`. -/
theorem reducedGegenbauer_one_eq (m δ : ℕ) :
    reducedGegenbauer m 1 δ = derivative (legendreP (2 * m + δ + 1)) /ₘ polyX ^ δ := by
  have h := iterate_derivative_legendreP_eq_gegenbauerC (2 * m + δ) 1
  have hd : (2 * 1 - 1).doubleFactorial = 1 := by norm_num [Nat.doubleFactorial]
  rw [hd, Nat.cast_one, map_one, one_mul, Function.iterate_one] at h
  rw [reducedGegenbauer_eq, Nat.cast_one, ← h]

/-- **Remark after Theorem 1.4.** For the derivative orders `r = 0` and `r = 1`, the polynomial
`F_{m,r,δ}` is irreducible over `ℚ` for every `m ≥ 1` and `δ ∈ {0,1}`. -/
theorem irreducible_reducedGegenbauer_of_le_one (hI : FirstDerivativeIntegerInequalities)
    (hF : FirstDerivativeFactorDegreeChecks) (hDeng : DengLegendreIrreducibility)
    (hH : HansonLcmBound) (hZ : JacobiSimpleRealZeros)
    {m r δ : ℕ} (hr : r ≤ 1) (hδ : δ ≤ 1) (hm : 1 ≤ m) :
    Irreducible (reducedGegenbauer m r δ) := by
  interval_cases r
  · rw [reducedGegenbauer_zero_eq]
    interval_cases δ
    · exact (hDeng m hm).1
    · exact (hDeng m hm).2
  · rw [reducedGegenbauer_one_eq]
    exact irreducible_derivative_legendreP hI hF hH hZ hδ hm

/-- `F_{m,r,δ}` is even: `F_{m,r,δ} = G(X²)` with `G = ∑_{k ≤ m} c_k X^{m-k}`, `c_k` the
coefficients of the explicit formula for `C_{2m+δ}^{r+1/2}`. -/
theorem reducedGegenbauer_eq_expand (m r δ : ℕ) (hδ : δ ≤ 1) :
    reducedGegenbauer m r δ = expand ℚ 2 (∑ k ∈ Finset.range (m + 1),
      C ((-1) ^ k * (ascPochhammer ℚ (2 * m + δ - k)).eval ((r : ℚ) + 1 / 2) /
        ((k.factorial : ℚ) * ((2 * m + δ - 2 * k).factorial : ℚ)) * 2 ^ (2 * m + δ - 2 * k)) *
          polyX ^ (m - k)) := by
  have hn : (2 * m + δ) / 2 = m := by omega
  have hsum : gegenbauerC ((r : ℚ) + 1 / 2) (2 * m + δ) = polyX ^ δ * expand ℚ 2
      (∑ k ∈ Finset.range (m + 1),
        C ((-1) ^ k * (ascPochhammer ℚ (2 * m + δ - k)).eval ((r : ℚ) + 1 / 2) /
          ((k.factorial : ℚ) * ((2 * m + δ - 2 * k).factorial : ℚ)) * 2 ^ (2 * m + δ - 2 * k)) *
            polyX ^ (m - k)) := by
    rw [gegenbauerC_eq, hn, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [map_mul (expand ℚ 2), expand_C, map_pow (expand ℚ 2), expand_X,
      ← pow_mul (polyX : ℚ[X]) 2 (m - k),
      show 2 * m + δ - 2 * k = δ + (m - k) * 2 by omega, pow_add (polyX : ℚ[X]) δ ((m - k) * 2)]
    ring
  rw [reducedGegenbauer_eq, hsum, mul_divByMonic_cancel_left _ (monic_X_pow δ)]

/-- `Q_{m,r,δ}` is irreducible whenever `F_{m,r,δ}(x) = Q_{m,r,δ}(x²)` is. -/
theorem irreducible_reducedGegenbauerSquare_of_irreducible {m r δ : ℕ} (hδ : δ ≤ 1)
    (h : Irreducible (reducedGegenbauer m r δ)) : Irreducible (reducedGegenbauerSquare m r δ) := by
  rw [reducedGegenbauer_eq_expand m r δ hδ] at h
  rw [reducedGegenbauerSquare_eq, reducedGegenbauer_eq_expand m r δ hδ,
    contract_expand 2 two_ne_zero]
  exact of_irreducible_expand two_ne_zero h

/-- **Remark after Corollary 1.7.** For `r ≤ 1`, `Q_{m,r,δ}` is irreducible over `ℚ` for every
`m ≥ 1` and `δ ∈ {0,1}`. -/
theorem irreducible_reducedGegenbauerSquare_of_le_one (hI : FirstDerivativeIntegerInequalities)
    (hF : FirstDerivativeFactorDegreeChecks) (hDeng : DengLegendreIrreducibility)
    (hH : HansonLcmBound) (hZ : JacobiSimpleRealZeros)
    {m r δ : ℕ} (hr : r ≤ 1) (hδ : δ ≤ 1) (hm : 1 ≤ m) :
    Irreducible (reducedGegenbauerSquare m r δ) :=
  irreducible_reducedGegenbauerSquare_of_irreducible hδ
    (irreducible_reducedGegenbauer_of_le_one hI hF hDeng hH hZ hr hδ hm)

/-- **Remark after Corollary 1.7.** For `r = 0` and `E = ℚ`, Theorem 1.2 gives the Galois group
`Gal(F_{m,0,δ}/ℚ) = W_m` in every degree `m ≥ 1`. -/
theorem galoisGroupIsWreath_reducedGegenbauer_zero (hDeng : DengLegendreIrreducibility)
    (hBMOR : BMORPrimeCountingBound) (hBT : BrunTitchmarshInequality)
    (hJones : JonesCycleTheorem) (hCHL : CullinanHajirLegendreGalois)
    (hCHL4 : PrimesModFourInDyadicInterval) {m δ : ℕ} (hm : 1 ≤ m) (hδ : δ ≤ 1) :
    GaloisGroupIsWreath (reducedGegenbauer m 0 δ) := by
  rw [reducedGegenbauer_zero_eq]
  exact legendreGaloisStatement hDeng hBMOR hBT hJones hCHL hCHL4 m δ hm hδ

end ArithmeticOfJacobiPolynomials
