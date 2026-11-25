/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.SymmetricIrreducibility
public import ArithmeticOfJacobiPolynomials.Jacobi.DerivativeIntegerCriterion
public import ArithmeticOfJacobiPolynomials.Jacobi.SymmetricCoefficients
public import ArithmeticOfJacobiPolynomials.Polynomial.FactorDegrees
public import ArithmeticOfJacobiPolynomials.External
public import ArithmeticOfJacobiPolynomials.MainResults

/-!
# Theorem 1.5 (Legendre polynomials and their first derivatives)

For every `m ≥ 1`, `P_{2m}`, `P_{2m+1}/x`, `P'_{2m+1}` and `P'_{2m+2}/x` are irreducible over
`ℚ`. The first two assertions are [Deng, Theorem 1.1] (`DengLegendreIrreducibility`). For the
derivatives (`r = 1` in Theorem 3.4):
* `m ≥ 200`: `irreducible_derivative_legendreP_of_two_hundred_le` (the exact criterion, proved);
* `1 ≤ m ≤ 199`, `m ∉ E_δ` (318 pairs): the integer inequality (C.2), a computed statement
  (`FirstDerivativeIntegerInequalities`), turned into irreducibility by the proved reduction
  `irreducible_derivative_legendreP_of_integer_inequality`;
* `m ∈ E_δ` (80 pairs): the computed factor-degree checks (`FirstDerivativeFactorDegreeChecks`),
  turned into irreducibility by the proved Lemma C.1 (`irreducible_of_factorDegrees`) and the
  proved identification of `P'_{2m+δ+1}/x^δ` with a rational multiple of `H_{2m+δ}`
  (`derivative_legendreP_divByMonic_eq_coefficientPoly`).

The two computed statements are inputs in the `ComputerVerified` section of `External.lean`.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial FirstDerivativeCriterion

/-- **`P'_{2m+δ+1}/x^δ` is a rational multiple of `H_{2m+δ}`.** For `δ ≤ 1`,
`P'_{2m+δ+1}(x)/x^δ = 2^{-(2m+δ+1)} ∑_{k=0}^m (-1)^k (2n+2-2k)! / (k! (n+1-k)! (n-2k)!) x^{n-2k-δ}`
with `n = 2m + δ` (the coefficient formula (Appendix C.2) of Lemma C.2). -/
theorem derivative_legendreP_divByMonic_eq_coefficientPoly (m δ : ℕ) (hδ : δ ≤ 1) :
    derivative (legendreP (2 * m + δ + 1)) /ₘ polyX ^ δ =
      C ((1 / 2 : ℚ) ^ (2 * m + δ + 1)) * finiteDerivativeCoefficientPoly m δ := by
  have hfac := X_pow_mul_iterate_derivative_legendreP_divByMonic m 1 δ hδ
  simp only [Function.iterate_one] at hfac
  have hcoeff : ∀ i, (derivative (legendreP (2 * m + δ + 1)) /ₘ polyX ^ δ).coeff i =
      (derivative (legendreP (2 * m + δ + 1))).coeff (i + δ) := by
    intro i
    conv_rhs => rw [← hfac]
    rw [coeff_X_pow_mul]
  ext i
  rw [hcoeff, coeff_C_mul, finiteDerivativeCoefficientPoly_eq, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases hi : i ≤ 2 * m ∧ i % 2 = 0
  · obtain ⟨hi1, hi2⟩ := hi
    have hk : m - i / 2 ≤ (2 * m + δ) / 2 := by omega
    have h := coeff_iterate_derivative_legendreP (2 * m + δ) 1 (m - i / 2) hk
    simp only [Function.iterate_one] at h
    have hidx : 2 * m + δ - 2 * (m - i / 2) = i + δ := by omega
    have h2 : (derivative (legendreP (2 * m + δ + 1))).coeff (i + δ) =
        (derivative (legendreP (2 * m + δ + 1))).coeff (2 * m + δ - 2 * (m - i / 2)) := by
      rw [hidx]
    have e : 2 * (2 * m + δ) + 2 * 1 - 2 * (m - i / 2) =
        2 * (2 * m + δ) + 2 - 2 * (m - i / 2) := by omega
    rw [e] at h
    rw [h2, h, Finset.sum_eq_single (m - i / 2)]
    · have hc : (i = 2 * m + δ - 2 * (m - i / 2) - δ) = True := eq_true (by omega)
      simp only [hc, ↓reduceIte]
    · intro j hj hjk
      have := Finset.mem_range.mp hj
      have hc : (i = 2 * m + δ - 2 * j - δ) = False := eq_false (by omega)
      simp only [hc, ↓reduceIte]
    · intro hk'
      exact absurd (Finset.mem_range.mpr (by omega)) hk'
  · rw [Finset.sum_eq_zero, mul_zero]
    · by_cases hi1 : i ≤ 2 * m
      · have hodd : i % 2 = 1 := by omega
        have := coeff_iterate_derivative_legendreP_eq_zero_of_odd (2 * m + δ) 1 (i + δ)
          ⟨m + δ + i / 2, by omega⟩
        simpa only [Function.iterate_one] using this
      · apply coeff_eq_zero_of_natDegree_lt
        have := natDegree_iterate_derivative_legendreP_le (2 * m + δ) 1
        simp only [Function.iterate_one] at this
        omega
    · intro k hk
      have := Finset.mem_range.mp hk
      have hc : (i = 2 * m + δ - 2 * k - δ) = False := eq_false (by omega)
      simp only [hc, ↓reduceIte]

/-- **Lemma C.2, the `80` pairs `m ∈ E_δ`.** From the computed factor-degree checks and
Lemma C.1 (`irreducible_of_factorDegrees`): `P'_{2m+δ+1}/x^δ` is irreducible over `ℚ`. -/
theorem irreducible_derivative_legendreP_of_mem_exceptional
    (hF : FirstDerivativeFactorDegreeChecks) {m δ : ℕ} (hδ : δ ≤ 1) (hm : 1 ≤ m)
    (hm' : m ≤ 199) (hE : m ∈ exceptionalIndices δ) :
    Irreducible (derivative (legendreP (2 * m + δ + 1)) /ₘ polyX ^ δ) := by
  obtain ⟨H, hprim, -, hdeg, ⟨c, hc, hHc⟩, P, hP, hsums⟩ := hF m δ hm hm' hδ hE
  have hirr : Irreducible (H.map (Int.castRingHom ℚ)) := by
    refine irreducible_of_factorDegrees H hprim (by omega) P (fun p hp => (hP p hp).1)
      (fun p hp => (hP p hp).2.2.1.trans hdeg.symm) (fun p hp => (hP p hp).2.2.2) ?_
    intro k hk1 hk2
    exact hsums k hk1 (by omega)
  rw [derivative_legendreP_divByMonic_eq_coefficientPoly m δ hδ]
  have hpoly : finiteDerivativeCoefficientPoly m δ = C c⁻¹ * H.map (Int.castRingHom ℚ) := by
    rw [hHc, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul]
  rw [hpoly, ← mul_assoc, ← C_mul]
  have hu : IsUnit (C ((1 / 2 : ℚ) ^ (2 * m + δ + 1) * c⁻¹)) :=
    isUnit_C.mpr (Ne.isUnit (mul_ne_zero (pow_ne_zero _ (by norm_num)) (inv_ne_zero hc)))
  exact (irreducible_isUnit_mul hu).mpr hirr

/-- **Lemma C.2.** For `1 ≤ m ≤ 199` and `δ ∈ {0,1}`,
`P'_{2m+δ+1}(x)/x^δ` is irreducible over `ℚ`: the 318 pairs outside `E_δ` by the integer
inequality (C.2) (computed input `FirstDerivativeIntegerInequalities`), the 80 pairs in `E_δ` by
Lemma C.1 (computed input `FirstDerivativeFactorDegreeChecks`). -/
theorem irreducible_derivative_legendreP_of_le_199 (hI : FirstDerivativeIntegerInequalities)
    (hF : FirstDerivativeFactorDegreeChecks) (hZ : JacobiSimpleRealZeros)
    {m δ : ℕ} (hδ : δ ≤ 1) (hm : 1 ≤ m) (hm' : m ≤ 199) :
    Irreducible (derivative (legendreP (2 * m + δ + 1)) /ₘ polyX ^ δ) := by
  by_cases hE : m ∈ exceptionalIndices δ
  · exact irreducible_derivative_legendreP_of_mem_exceptional hF hδ hm hm' hE
  · obtain ⟨hm4, hlt⟩ := hI m δ hm hm' hδ hE
    exact irreducible_derivative_legendreP_of_integer_inequality hZ hδ hm4 hlt

/-- **First derivatives of Legendre polynomials** (Theorem 1.5, last two assertions): for
`m ≥ 1` and `δ ∈ {0,1}`, `P'_{2m+δ+1}(x)/x^δ` is irreducible over `ℚ`. -/
theorem irreducible_derivative_legendreP (hI : FirstDerivativeIntegerInequalities)
    (hF : FirstDerivativeFactorDegreeChecks) (hH : HansonLcmBound)
    (hZ : JacobiSimpleRealZeros) {m δ : ℕ} (hδ : δ ≤ 1)
    (hm : 1 ≤ m) : Irreducible (derivative (legendreP (2 * m + δ + 1)) /ₘ polyX ^ δ) := by
  by_cases h200 : 200 ≤ m
  · exact irreducible_derivative_legendreP_of_two_hundred_le hH hZ hδ h200
  · exact irreducible_derivative_legendreP_of_le_199 hI hF hZ hδ hm (by omega)

/-- **Theorem 1.5.** For every `m ≥ 1`, `P_{2m}`, `P_{2m+1}/x`, `P'_{2m+1}` and `P'_{2m+2}/x`
are irreducible over `ℚ`. -/
theorem legendreAndDerivativesStatement (hI : FirstDerivativeIntegerInequalities)
    (hF : FirstDerivativeFactorDegreeChecks) (hDeng : DengLegendreIrreducibility)
    (hH : HansonLcmBound) (hZ : JacobiSimpleRealZeros) :
    LegendreAndDerivativesStatement := by
  intro m hm
  obtain ⟨h0, h1⟩ := hDeng m hm
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : reducedLegendre m 0 = legendreP (2 * m) := by
      rw [reducedLegendre_eq, pow_zero, divByMonic_one, add_zero]
    rwa [e] at h0
  · rwa [reducedLegendre_eq, pow_one] at h1
  · have h := irreducible_derivative_legendreP hI hF hH hZ (δ := 0) (by norm_num) hm
    rwa [pow_zero, divByMonic_one, add_zero] at h
  · have h := irreducible_derivative_legendreP hI hF hH hZ (δ := 1) le_rfl hm
    rwa [pow_one, show 2 * m + 1 + 1 = 2 * m + 2 by ring] at h

end ArithmeticOfJacobiPolynomials
