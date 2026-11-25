module

public import ArithmeticOfJacobiPolynomials.Verification.DerivativeCoefficientFormula
public import ArithmeticOfJacobiPolynomials.Verification.DerivativeCoeffs
public import ArithmeticOfJacobiPolynomials.Verification.Frobenius
public import ArithmeticOfJacobiPolynomials.Jacobi.LegendreDerivatives

/-! # Coefficient certificates for the exceptional first derivatives

The common nonzero scalar is checked coefficient by coefficient against the factorial
formula of Appendix C. This identifies the integer polynomial used in a certificate
with the required normalized derivative over the rationals.
-/

public section

namespace ArithmeticOfJacobiPolynomials.DerivativeModel

open Polynomial Finset

theorem coeff_finiteDerivativeCoefficientPoly (m δ i : ℕ) :
    (finiteDerivativeCoefficientPoly m δ).coeff i = targetCoeff m δ i := by
  rw [finiteDerivativeCoefficientPoly_eq, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  change (∑ k ∈ range (m + 1),
    if i = 2 * m + δ - 2 * k - δ then termCoeff m δ k else 0) = _
  unfold targetCoeff
  split_ifs with h
  · rw [sum_eq_single (m - i / 2)]
    · rw [ite_eq_left (by omega)]
    · intro k hk hne
      have := mem_range.mp hk
      rw [ite_eq_right (by omega)]
    · intro hn
      exact False.elim (hn (mem_range.mpr (by omega)))
  · apply sum_eq_zero
    intro k hk
    have := mem_range.mp hk
    rw [ite_eq_right (by omega)]

/-- A finite coefficient gcd suffices to identify a primitive integer model. -/
theorem isPrimitive_of_coefficient_gcd (l : List ℤ) (d : ℕ)
    (hlen : l.length = d + 1) (hlc : l.getD d 0 ≠ 0)
    (hg : (range l.length).gcd (fun i => l.getD i 0) = 1) :
    (ofCoeffs l).IsPrimitive := by
  rw [isPrimitive_iff_content_eq_one, content_eq_gcd_range_of_lt (ofCoeffs l) l.length
    (by rw [natDegree_ofCoeffs l d hlen hlc, hlen]; exact Nat.lt_succ_self _)]
  have he : (fun i => (ofCoeffs l).coeff i) = fun i => l.getD i 0 := funext (coeff_ofCoeffs l)
  change (range l.length).gcd (fun i => (ofCoeffs l).coeff i) = 1
  rwa [he]

/-- The coefficient checks identify a given integer model up to the indicated scale. -/
theorem eq_scaled_model (m δ : ℕ) (l : List ℤ) (scale : ℕ)
    (hlen : l.length = 2 * m + 1)
    (hcoeff : ∀ i : Fin (2 * m + 1),
      (scale : ℚ) * (l.getD i.val 0 : ℚ) = targetCoeff m δ i.val) :
    finiteDerivativeCoefficientPoly m δ =
      C (scale : ℚ) * (ofCoeffs l).map (Int.castRingHom ℚ) := by
  ext i
  rw [coeff_finiteDerivativeCoefficientPoly, coeff_C_mul, coeff_map, coeff_ofCoeffs]
  change targetCoeff m δ i = (scale : ℚ) * (l.getD i 0 : ℚ)
  by_cases hi : i < 2 * m + 1
  · exact (hcoeff ⟨i, hi⟩).symm
  · rw [List.getD_eq_default _ _ (hlen ▸ Nat.le_of_not_gt hi)]
    simp [targetCoeff, show ¬ i ≤ 2 * m by omega]

/-- Irreducibility of a checked integer model over the rationals gives irreducibility
of the normalized first derivative in Lemma C.2. -/
theorem irreducible_derivative_of_model {m δ : ℕ} (hδ : δ ≤ 1) (l : List ℤ) (scale : ℕ)
    (hs : scale ≠ 0) (hlen : l.length = 2 * m + 1)
    (hcoeff : ∀ i : Fin (2 * m + 1),
      (scale : ℚ) * (l.getD i.val 0 : ℚ) = targetCoeff m δ i.val)
    (hirr : Irreducible ((ofCoeffs l).map (Int.castRingHom ℚ))) :
    Irreducible (derivative (legendreP (2 * m + δ + 1)) /ₘ Polynomial.X ^ δ) := by
  rw [derivative_legendreP_divByMonic_eq_coefficientPoly m δ hδ,
    eq_scaled_model m δ l scale hlen hcoeff, ← mul_assoc, ← C_mul]
  exact (irreducible_isUnit_mul (isUnit_C.mpr (Ne.isUnit (mul_ne_zero
    (pow_ne_zero _ (by norm_num)) (by exact_mod_cast hs))))).mpr hirr

/-- A degree-preserving irreducible reduction suffices for the primitive coefficient model. -/
theorem irreducible_derivative_of_certificate {m δ : ℕ} (hm : 1 ≤ m) (hδ : δ ≤ 1)
    (l : List ℤ) (scale : ℕ) (hs : scale ≠ 0) (hlen : l.length = 2 * m + 1)
    (hcoeff : ∀ i : Fin (2 * m + 1),
      (scale : ℚ) * (l.getD i.val 0 : ℚ) = targetCoeff m δ i.val)
    (hg : (range l.length).gcd (fun i => l.getD i 0) = 1)
    (p : ℕ) [Fact p.Prime] (hlc : ((l.getD (2 * m) 0 : ℤ) : ZMod p) ≠ 0)
    (hirr : Irreducible (ofCoeffs (l.map (Int.castRingHom (ZMod p))))) :
    Irreducible (derivative (legendreP (2 * m + δ + 1)) /ₘ Polynomial.X ^ δ) := by
  apply irreducible_derivative_of_model hδ l scale hs hlen hcoeff
  have ht : l.getD (2 * m) 0 ≠ 0 := by
    intro h
    exact hlc (by rw [h, Int.cast_zero])
  have hd := natDegree_ofCoeffs l (2 * m) hlen ht
  apply irreducible_of_irreducible_reduction (ofCoeffs l)
    (isPrimitive_of_coefficient_gcd l (2 * m) hlen ht hg) p (by omega)
  · apply natDegree_map_of_leadingCoeff_ne_zero
    simpa only [leadingCoeff, hd, coeff_ofCoeffs, Int.coe_castRingHom] using hlc
  · rwa [map_ofCoeffs]

end ArithmeticOfJacobiPolynomials.DerivativeModel
