/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.BadPrimes
public import ArithmeticOfJacobiPolynomials.KanekoZagier.PrimitiveIrreducibility

/-!
# Proposition 4.6: the error beyond the bilinear terms is `O(k log n)`

The digit sums in Proposition 4.6 (`padicValInt_two_resultant_le`,
`padicValInt_three_resultant_le`) are bounded by `s_b(m) ≤ (b - 1)(⌊log_b m⌋ + 1)`
(`digits_sum_le_mul_log`), so the error beyond `min(⋯) + ke/p` is at most
`(k/2)(⌊log_2 n⌋ + 1)` at `p = 2` and `(k/3)(⌊log_3 (2n+δ)⌋ + 1)` at `p = 3`, uniformly in the
factorization.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-- **Proposition 4.6 at `p = 2`, with the `O(k log n)` error made explicit.** -/
theorem padicValInt_two_resultant_le_log
    (hNP : NewtonPolygonRootSlopes) {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) {n : ℕ} (hn : n ≠ 0) {H A B : ℤ[X]} {c : ℚ} (hc : c ≠ 0)
    (hH : H.map (Int.castRingHom ℚ) = C c * jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n)
    (hlc : ¬ (2 : ℤ) ∣ H.leadingCoeff) (hAB : H = A * B) :
    (padicValInt 2 (resultant A B) : ℝ) ≤
      min ((B.natDegree : ℝ) * padicValInt 2 (A.eval 0))
          ((A.natDegree : ℝ) * padicValInt 2 (B.eval 0)) +
        (A.natDegree : ℝ) * B.natDegree / 2 + (A.natDegree : ℝ) / 2 * (Nat.log 2 n + 1) := by
  have h := padicValInt_two_resultant_le hNP hl hμ hc hH hlc hAB
  have hd : ((Nat.digits 2 n).sum : ℝ) ≤ Nat.log 2 n + 1 := by
    have h0 := digits_sum_le_mul_log (b := 2) (by norm_num) hn
    have h2 : (Nat.digits 2 n).sum ≤ Nat.log 2 n + 1 := by simpa using h0
    exact_mod_cast h2
  have hk : (0 : ℝ) ≤ (A.natDegree : ℝ) / 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hd hk]

/-- **Proposition 4.6 at `p = 3`, with the `O(k log n)` error made explicit.** -/
theorem padicValInt_three_resultant_le_log
    (hNP : NewtonPolygonRootSlopes) {l μ : ℤ} (hl : l = 1 ∨ l = -1) {δ : ℕ}
    (hδ : δ ≤ 1) (hμ : μ = 2 * δ - 1) {n : ℕ} (hn : n ≠ 0) {H A B : ℤ[X]} {c : ℚ}
    (hc : c ≠ 0)
    (hH : H.map (Int.castRingHom ℚ) = C c * jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n)
    (hlc : ¬ (3 : ℤ) ∣ H.leadingCoeff) (hAB : H = A * B) :
    (padicValInt 3 (resultant A B) : ℝ) ≤
      min ((B.natDegree : ℝ) * padicValInt 3 (A.eval 1))
          ((A.natDegree : ℝ) * padicValInt 3 (B.eval 1)) +
        (A.natDegree : ℝ) * B.natDegree / 3 +
          (A.natDegree : ℝ) / 3 * (Nat.log 3 (2 * n + δ) + 1) := by
  have h := padicValInt_three_resultant_le hNP hl hδ hμ hc hH hlc hAB
  have hd : (digitSum3 (2 * n + δ) : ℝ) ≤ 2 * (Nat.log 3 (2 * n + δ) + 1) := by
    have h0 := digits_sum_le_mul_log (b := 3) (by norm_num) (show 2 * n + δ ≠ 0 by omega)
    have h2 : (Nat.digits 3 (2 * n + δ)).sum ≤ 2 * (Nat.log 3 (2 * n + δ) + 1) := by
      simpa using h0
    rw [digitSum3_eq]
    exact_mod_cast h2
  have hk : (0 : ℝ) ≤ (A.natDegree : ℝ) / 6 := by positivity
  have := mul_le_mul_of_nonneg_left hd hk
  nlinarith

end ArithmeticOfJacobiPolynomials
