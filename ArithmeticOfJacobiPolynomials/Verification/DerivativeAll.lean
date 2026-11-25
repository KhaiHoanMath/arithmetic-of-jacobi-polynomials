module

public import ArithmeticOfJacobiPolynomials.Verification.DerivativeCertificates
public import ArithmeticOfJacobiPolynomials.Verification.RabinModel
public import ArithmeticOfJacobiPolynomials.Verification.RabinFastModel
public import ArithmeticOfJacobiPolynomials.Verification.Rabin.Case0_11
public import ArithmeticOfJacobiPolynomials.Verification.Rabin.Case0_23
public import ArithmeticOfJacobiPolynomials.Verification.Rabin.Case0_46
public import ArithmeticOfJacobiPolynomials.Verification.Rabin.Case1_17
public import ArithmeticOfJacobiPolynomials.Verification.Rabin.Case1_22
public import ArithmeticOfJacobiPolynomials.Verification.Rabin.Case1_25
public import ArithmeticOfJacobiPolynomials.Verification.Rabin.Case1_32
public import ArithmeticOfJacobiPolynomials.Verification.Rabin.Case1_38
public import ArithmeticOfJacobiPolynomials.Verification.Rabin.Case1_43
public import ArithmeticOfJacobiPolynomials.Verification.Rabin.Case1_45
public import ArithmeticOfJacobiPolynomials.Verification.Rabin.Case1_47

/-! # All exceptional first derivatives

The Eisenstein tests settle 69 indices. Each of the other eleven has one full-degree
irreducible reduction, verified by explicit powers and inverses in the quotient.
Together with the size inequalities these give Theorem 1.5 and Corollary 6.2.
-/

public section
namespace ArithmeticOfJacobiPolynomials

open Polynomial DerivativeModel ModularArithmetic

private theorem derivative_of_record (c : RabinData) (hm : 1 ≤ c.m) (hδ : c.δ ≤ 1)
    (hp : c.p.Prime)
    (hc : Conditions c.m c.δ c.p c.scale c.coeffs c.f c.xp c.tabs c.row c.inv c.chainAt
      c.expAt c.opAt c.operations.length) :
    Irreducible (derivative (legendreP (2 * c.m + c.δ + 1)) /ₘ Polynomial.X ^ c.δ) := by
  let : Fact c.p.Prime := ⟨hp⟩
  exact irreducible_encoded hm hδ hc

private theorem derivative_of_fast_record (c : RabinData) (a : FastRabinData)
    (hm : 1 ≤ c.m) (hδ : c.δ ≤ 1) (hp : c.p.Prime)
    (hc : FastConditions c.m c.δ c.p c.scale c.coeffs c.f c.xp c.tabs c.row c.inv c.chainAt
      c.expAt c.opAt c.operations.length (a.qAt c) (a.plusAt c) (a.minusAt c) a.packed a.sums
      (a.carryAt c)) :
    Irreducible (derivative (legendreP (2 * c.m + c.δ + 1)) /ₘ Polynomial.X ^ c.δ) := by
  let : Fact c.p.Prime := ⟨hp⟩
  exact irreducible_encoded_fast hm hδ hc

/-- All eleven residual derivative cases have certified irreducible reductions. -/
theorem remainingDerivativeChecks_proved : RemainingDerivativeChecks := by
  intro m δ hδ hm
  interval_cases δ
  · simp only [DerivativeModel.remainingIndices, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact derivative_of_record case0_11 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) case0_11Checked
    · exact derivative_of_record case0_23 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) case0_23Checked
    · exact derivative_of_fast_record case0_46 case0_46Fast (by decide +kernel) (by decide +kernel)
        (by decide +kernel) case0_46Checked
  · simp only [DerivativeModel.remainingIndices, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact derivative_of_record case1_17 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) case1_17Checked
    · exact derivative_of_record case1_22 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) case1_22Checked
    · exact derivative_of_record case1_25 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) case1_25Checked
    · exact derivative_of_fast_record case1_32 case1_32Fast (by decide +kernel) (by decide +kernel)
        (by decide +kernel) case1_32Checked
    · exact derivative_of_fast_record case1_38 case1_38Fast (by decide +kernel) (by decide +kernel)
        (by decide +kernel) case1_38Checked
    · exact derivative_of_fast_record case1_43 case1_43Fast (by decide +kernel) (by decide +kernel)
        (by decide +kernel) case1_43Checked
    · exact derivative_of_fast_record case1_45 case1_45Fast (by decide +kernel) (by decide +kernel)
        (by decide +kernel) case1_45Checked
    · exact derivative_of_fast_record case1_47 case1_47Fast (by decide +kernel) (by decide +kernel)
        (by decide +kernel) case1_47Checked

/-- Theorem 1.5 with the finite comparisons and modular checks proved in Lean. -/
theorem legendreAndDerivatives_verified (hHW : HoltWahabLegendreIrreducibility)
    (hH : HansonLcmBound) (hZ : JacobiSimpleRealZeros) : LegendreAndDerivativesStatement :=
  legendreAndDerivatives_of_remaining hHW hH hZ remainingDerivativeChecks_proved

/-- Corollary 6.2 with the finite comparisons and modular checks proved in Lean. -/
theorem commonRoots_verified (hHW : HoltWahabLegendreIrreducibility)
    (hH : HansonLcmBound) (hZ : JacobiSimpleRealZeros) : CommonRootsStatement :=
  commonRoots_of_remaining hHW hH hZ remainingDerivativeChecks_proved

end ArithmeticOfJacobiPolynomials
