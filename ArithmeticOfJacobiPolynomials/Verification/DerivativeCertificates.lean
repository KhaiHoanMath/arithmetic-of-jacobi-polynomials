module

public import ArithmeticOfJacobiPolynomials.Verification.DerivativeModel
public import ArithmeticOfJacobiPolynomials.Verification.DerivativeEisenstein
public import ArithmeticOfJacobiPolynomials.Verification.DerivativeEisensteinData
public import ArithmeticOfJacobiPolynomials.Verification.Legendre

/-! # Eisenstein checks for the exceptional derivatives of Appendix C

Of the 80 exceptional polynomials, 69 satisfy Eisenstein's criterion in one of
the two coefficient orders. The integers below specify primes; a negative sign
indicates that the prime is applied to the reciprocal polynomial.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial FirstDerivativeCriterion DerivativeModel

namespace DerivativeModel

open EisensteinData

/-- For each of the 69 exceptional polynomials with an Eisenstein prime in either
coefficient order, the normalized derivative is irreducible over the rationals. -/
theorem irreducible_derivative_of_eisenstein_index {m δ : ℕ} (hδ : δ ≤ 1) (hm : m ≤ 199)
    (he : m ∈ exceptionalIndices δ) (hr : m ∉ remainingIndices δ) :
    Irreducible (derivative (legendreP (2 * m + δ + 1)) /ₘ Polynomial.X ^ δ) := by
  have h := certificates ⟨m, by omega⟩ ⟨δ, by omega⟩
  rcases h with h | h | h
  · exact (h he).elim
  · exact (hr h).elim
  obtain ⟨hm0, hp, hs, hlen, hlc, hc, hg, hlead, hcoeff, hconst⟩ := h
  apply irreducible_derivative_of_model hδ _ _ hs hlen hc
  apply irreducible_of_eisenstein_coeffs
    (isPrimitive_of_coefficient_gcd _ _ hlen hlc hg) (natDegree_ofCoeffs _ _ hlen hlc)
    (by omega) hp (decide (signedPrime m δ < 0))
  · simpa only [coeff_ofCoeffs] using hlead
  · simpa only [coeff_ofCoeffs] using hcoeff
  · simpa only [coeff_ofCoeffs] using hconst

/-- The eleven residual first derivatives after the Eisenstein and size comparisons. -/
@[expose] def RemainingDerivativeChecks : Prop :=
  ∀ m δ : ℕ, δ ≤ 1 → m ∈ remainingIndices δ →
    Irreducible (derivative (legendreP (2 * m + δ + 1)) /ₘ Polynomial.X ^ δ)

/-- Irreducibility of every normalized first derivative follows from the eleven
residual cases and the two cited results used by the size comparison. -/
theorem irreducible_derivative_of_remaining (hR : RemainingDerivativeChecks)
    (hH : HansonLcmBound) (hZ : JacobiSimpleRealZeros) {m δ : ℕ} (hm : 1 ≤ m) (hδ : δ ≤ 1) :
    Irreducible (derivative (legendreP (2 * m + δ + 1)) /ₘ Polynomial.X ^ δ) := by
  by_cases hbig : 200 ≤ m
  · exact irreducible_derivative_legendreP_of_two_hundred_le hH hZ hδ hbig
  by_cases he : m ∈ exceptionalIndices δ
  · by_cases hr : m ∈ remainingIndices δ
    · exact hR m δ hδ hr
    · exact irreducible_derivative_of_eisenstein_index hδ (by omega) he hr
  obtain ⟨hm4, hlt⟩ := firstDerivative_integer_inequalities hm (by omega) hδ he
  exact irreducible_derivative_legendreP_of_integer_inequality hZ hδ hm4 hlt

end DerivativeModel

/-- Theorem 1.5 using eleven exceptional derivative checks. -/
theorem legendreAndDerivatives_of_remaining (hHW : HoltWahabLegendreIrreducibility)
    (hH : HansonLcmBound) (hZ : JacobiSimpleRealZeros)
    (hR : DerivativeModel.RemainingDerivativeChecks) :
    LegendreAndDerivativesStatement := by
  intro m hm
  obtain ⟨h₀, h₁⟩ := legendreIrreducibility_of_comparison hHW hH hZ m hm
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [reducedLegendre_eq, pow_zero, divByMonic_one, add_zero] using h₀
  · simpa only [reducedLegendre_eq, pow_one] using h₁
  · simpa only [pow_zero, divByMonic_one, add_zero] using
      DerivativeModel.irreducible_derivative_of_remaining hR hH hZ hm (δ := 0) (by decide)
  · simpa only [pow_one, show 2 * m + 1 + 1 = 2 * m + 2 by omega] using
      DerivativeModel.irreducible_derivative_of_remaining hR hH hZ hm (δ := 1) le_rfl

/-- Corollary 6.2 with the same eleven exceptional derivative checks. -/
theorem commonRoots_of_remaining (hHW : HoltWahabLegendreIrreducibility)
    (hH : HansonLcmBound) (hZ : JacobiSimpleRealZeros)
    (hR : DerivativeModel.RemainingDerivativeChecks) :
    CommonRootsStatement :=
  commonRootsStatement_of_irreducible hH hZ (legendreAndDerivatives_of_remaining hHW hH hZ hR)

end ArithmeticOfJacobiPolynomials
