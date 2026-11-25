module

public import ArithmeticOfJacobiPolynomials.Verification.FiniteArithmetic
public import ArithmeticOfJacobiPolynomials.Verification.Frobenius
public import ArithmeticOfJacobiPolynomials.Verification.LegendrePrimePairs
public import ArithmeticOfJacobiPolynomials.Jacobi.SymmetricIrreducibility
public import ArithmeticOfJacobiPolynomials.Jacobi.DerivativeIntegerCriterion
public import ArithmeticOfJacobiPolynomials.Remarks.DerivativeOrders
public import ArithmeticOfJacobiPolynomials.Applications.CommonRootFiniteness

/-!
# The all-degree Legendre statements

The published Holt–Wahab theorem treats the degrees near an odd prime.
For the remaining small degrees we apply the paper's exact criterion at order zero.
For half-degree at least 100 we use the comparison already proved in the main development.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Finset Real FirstDerivativeCriterion

/-- Holt–Wahab, in the form of Cullinan–Hajir, *On the Galois groups of Legendre
polynomials*, Corollary 3.4(b), restricted to half-degrees below 100.
The original Legendre degree is `2*m+δ`. -/
@[expose] def HoltWahabLegendreIrreducibility : Prop :=
  ∀ m δ p : ℕ, 1 ≤ m → m < 100 → δ ≤ 1 → p.Prime → p ≠ 2 → p ≤ 2 * m + δ + 4 →
    2 * m + δ ≤ p + 3 → Irreducible (reducedLegendre m δ)

private theorem legendre_exact_of_integer {m δ : ℕ} (hm : 4 ≤ m)
    (hc : 64 * m * legendrePrimeProduct m δ ^ 2 < 16 ^ m) :
    primePowerLogSum m ((2 * (2 * m + δ) + 1 : ℕ) : ℝ) + log (8 * √(m : ℝ)) <
      m * log 4 := by
  have hz : 0 < legendrePrimeProduct m δ :=
    prod_pos fun p hp => pow_pos (mem_primes_le hp).pos _
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hzR : (0 : ℝ) < legendrePrimeProduct m δ := by exact_mod_cast hz
  have h8 : (0 : ℝ) < 8 * √(m : ℝ) := by positivity
  have hs : (legendrePrimeProduct m δ : ℝ) * (8 * √(m : ℝ)) < (4 : ℝ) ^ m := by
    refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
    have hl : ((legendrePrimeProduct m δ : ℝ) * (8 * √(m : ℝ))) ^ 2 =
        64 * m * legendrePrimeProduct m δ ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hmR.le]
      ring
    have hr : ((4 : ℝ) ^ m) ^ 2 = 16 ^ m := by
      rw [← pow_mul, mul_comm m 2, pow_mul]
      norm_num
    rw [hl, hr]
    exact_mod_cast hc
  have hlog := Real.log_lt_log (mul_pos hzR h8) hs
  rw [Real.log_mul hzR.ne' h8.ne', Real.log_pow] at hlog
  have hprod : primePowerLogSum m ((2 * (2 * m + δ) + 1 : ℕ) : ℝ) =
      log (legendrePrimeProduct m δ) := by
    rw [primePowerLogSum_natCast_eq, legendrePrimeProduct,
      log_natCast_prod_pow _ (fun p hp => mem_primes_le hp)]
  rwa [hprod]

/-- Stieltjes' all-degree irreducibility from the comparison and the classical short interval. -/
theorem reducedLegendre_irreducible (hHW : HoltWahabLegendreIrreducibility) (hH : HansonLcmBound)
    (hZ : JacobiSimpleRealZeros) {m δ : ℕ} (hm : 1 ≤ m) (hδ : δ ≤ 1) :
    Irreducible (reducedLegendre m δ) := by
  by_cases h100 : 100 ≤ m
  · rw [← reducedGegenbauer_zero_eq]
    exact irreducible_reducedGegenbauer_zero_of_hundred_le hH hZ hδ h100
  rcases legendre_small_degree_cases hm (by omega) hδ with ⟨p, hp, h2, hL, hR⟩ | ⟨h4, hc⟩
  · exact hHW m δ p hm (by omega) hδ hp h2 hL hR
  · rw [← reducedGegenbauer_zero_eq]
    apply irreducible_reducedGegenbauer_of_exact_criterion hZ hδ (by simpa using h4)
    have hA : symmetricRatio (2 * m + δ) 0 = 1 := by
      rw [symmetricRatio_eq]
      simp only [mul_zero, add_zero]
      have hf : ((2 * m + δ).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
      rw [sq, div_self (mul_ne_zero hf hf)]
    have hpt : log (primeTruncation 1 m) = 0 := by rw [log_primeTruncation]; simp
    simpa [hA, hpt] using legendre_exact_of_integer h4 hc

/-- The all-degree irreducibility hypothesis in the original declarations, now derived. -/
theorem legendreIrreducibility_of_comparison (hHW : HoltWahabLegendreIrreducibility)
    (hH : HansonLcmBound) (hZ : JacobiSimpleRealZeros) : DengLegendreIrreducibility := fun _ hm =>
  ⟨reducedLegendre_irreducible hHW hH hZ hm (by decide),
   reducedLegendre_irreducible hHW hH hZ hm (by decide)⟩

/-- The two prime alternatives in Cullinan–Hajir, Theorem 1.7, in the paper's normalization.
The sign is `2δ-1` and the prime interval is `(n+1)/2 < q < n-2`. -/
@[expose] def CullinanHajirLegendrePrimeCriterion : Prop :=
  ∀ n δ q : ℕ, 2 < n → δ ≤ 1 → q.Prime → n+1 < 2*q → q+2 < n →
    ((2*q+2*δ-1).Prime ∨ (2*(2*n+1-q)+2*δ-1).Prime) →
    Irreducible ((legendreJ (2*(δ : ℤ)-1) n).map (Int.castRingHom ℚ)) →
      GaloisGroupIsSymmetric ((legendreJ (2*(δ : ℤ)-1) n).map (Int.castRingHom ℚ))

/-- The small-degree restriction of Cullinan–Hajir, Theorem 1.9(a). -/
@[expose] def CullinanHajirLegendreSmallDegrees : Prop :=
  ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → ∀ n : ℕ, 1 ≤ n → n ≤ 25 →
    Irreducible ((legendreJ ε n).map (Int.castRingHom ℚ)) →
      GaloisGroupIsSymmetric ((legendreJ ε n).map (Int.castRingHom ℚ))

/-- Recover the full published range of Theorem 1.9(a) from the prime criterion and
the small-degree calculation. The finite prime certificates are checked in Lean. -/
theorem legendreGalois_finite_range (hP : CullinanHajirLegendrePrimeCriterion)
    (hS : CullinanHajirLegendreSmallDegrees) : CullinanHajirLegendreGalois := by
  intro ε hε n hn hhi hirr
  by_cases h25 : n ≤ 25
  · exact hS ε hε n hn h25 hirr
  have go (δ : ℕ) (hδ : δ ≤ 1) (he : 2*(δ : ℤ)-1 = ε) :
      GaloisGroupIsSymmetric ((legendreJ ε n).map (Int.castRingHom ℚ)) := by
    obtain ⟨q, hq, hl, hr, hp⟩ := legendre_prime_pairs hδ (by omega : 26 ≤ n) hhi
    rw [← he] at hirr ⊢
    exact hP n δ q (by omega) hδ hq hl hr hp hirr
  rcases hε with h | h
  · exact go 1 (by decide) (by omega)
  · exact go 0 (by decide) (by omega)

/-- Theorem 1.2 with irreducibility supplied by the paper's comparison. -/
theorem legendreGalois_of_comparison (hHW : HoltWahabLegendreIrreducibility) (hH : HansonLcmBound)
    (hZ : JacobiSimpleRealZeros) (hBMOR : BMORPrimeCountingBound)
    (hBT : BrunTitchmarshInequality) (hJones : JonesCycleTheorem)
    (hP : CullinanHajirLegendrePrimeCriterion) (hS : CullinanHajirLegendreSmallDegrees)
    (hCHL4 : PrimesModFourInDyadicInterval) : LegendreGaloisStatement :=
  legendreGaloisStatement (legendreIrreducibility_of_comparison hHW hH hZ) hBMOR hBT hJones
    (legendreGalois_finite_range hP hS) hCHL4

/-- The integer hypothesis of Lemma C.2 as used by the original declarations. -/
theorem firstDerivativeIntegerInequalities_proved : FirstDerivativeIntegerInequalities :=
  fun _ _ hm hm' hδ he => firstDerivative_integer_inequalities hm hm' hδ he

open Polynomial in
/-- A single numerical Frobenius certificate suffices for the normalized derivative
that occurs in Lemma C.2. Here `H` is its primitive integral model. -/
theorem irreducible_derivative_legendreP_of_frobenius_reduction {m δ : ℕ}
    (hm : 1 ≤ m) (hδ : δ ≤ 1) (H : ℤ[X]) (hprim : H.IsPrimitive) (hdeg : H.natDegree = 2 * m)
    (c : ℚ) (hc : c ≠ 0)
    (hHc : H.map (Int.castRingHom ℚ) = C c * finiteDerivativeCoefficientPoly m δ)
    (p : ℕ) [Fact p.Prime] (hmod : (H.map (Int.castRingHom (ZMod p))).natDegree = H.natDegree)
    (hall : H.map (Int.castRingHom (ZMod p)) ∣ Polynomial.X ^ p ^ H.natDegree - Polynomial.X)
    (htest : ∀ q : ℕ, q.Prime → q ∣ H.natDegree →
      IsCoprime (H.map (Int.castRingHom (ZMod p)))
        (Polynomial.X ^ p ^ (H.natDegree / q) - Polynomial.X)) :
    Irreducible (derivative (legendreP (2 * m + δ + 1)) /ₘ Polynomial.X ^ δ) := by
  have hirr := irreducible_of_frobenius_reduction H hprim p (by omega) hmod hall htest
  rw [derivative_legendreP_divByMonic_eq_coefficientPoly m δ hδ]
  have hpoly : finiteDerivativeCoefficientPoly m δ = C c⁻¹ * H.map (Int.castRingHom ℚ) := by
    rw [hHc, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul]
  rw [hpoly, ← mul_assoc, ← C_mul]
  have hu : IsUnit (C ((1 / 2 : ℚ) ^ (2 * m + δ + 1) * c⁻¹)) :=
    isUnit_C.mpr (Ne.isUnit (mul_ne_zero (pow_ne_zero _ (by norm_num)) (inv_ne_zero hc)))
  exact (irreducible_isUnit_mul hu).mpr hirr

/-- Theorem 1.5 with kernel-checked integer comparisons and the finite factor-degree input. -/
theorem legendreAndDerivatives_of_comparison (hHW : HoltWahabLegendreIrreducibility)
    (hH : HansonLcmBound) (hZ : JacobiSimpleRealZeros) (hF : FirstDerivativeFactorDegreeChecks) :
    LegendreAndDerivativesStatement :=
  legendreAndDerivativesStatement firstDerivativeIntegerInequalities_proved hF
    (legendreIrreducibility_of_comparison hHW hH hZ) hH hZ

/-- Corollary 6.2 with the same inputs as Theorem 1.5. -/
theorem commonRoots_of_comparison (hHW : HoltWahabLegendreIrreducibility)
    (hH : HansonLcmBound) (hZ : JacobiSimpleRealZeros) (hF : FirstDerivativeFactorDegreeChecks) :
    CommonRootsStatement :=
  commonRootsStatement_of_irreducible hH hZ (legendreAndDerivatives_of_comparison hHW hH hZ hF)

end ArithmeticOfJacobiPolynomials
