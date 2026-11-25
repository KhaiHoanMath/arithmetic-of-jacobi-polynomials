module

public import ArithmeticOfJacobiPolynomials.Verification.DerivativeCoefficientFormula
public import ArithmeticOfJacobiPolynomials.Jacobi.LegendreDerivativeData
public import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-! # The finite integer tests for the 69 Eisenstein cases -/

public section

namespace ArithmeticOfJacobiPolynomials.DerivativeModel

open FirstDerivativeCriterion

/-- The indices still requiring a different criterion after the two Eisenstein tests. -/
@[expose] def remainingIndices : ℕ → List ℕ
  | 0 => [11, 23, 46]
  | _ => [17, 22, 25, 32, 38, 43, 45, 47]

namespace EisensteinData

@[expose] def signedPrime (m δ : ℕ) : ℤ :=
  let primes : List ℤ := if δ = 0 then
    [0, -5, -7, 5, 7, 3, 3, 13, -19, 17, 19, 0, 23, -29, -31, 5, 31, -37, 3, 37,
     -43, 41, 43, 0, 47, -53, 0, 0, 7, 0, 59, 61, -67, 0, 67, 0, 0, 73, 0, 0, 79, 0, 83,
     -89, 0, 89, 0, -97]
    else
    [0, 3, 5, 7, -13, 11, 13, -19, 17, 19, -5, 23, -29, -31, 29, 5, -37, 0, 3,
     -43, 41, 43, 0, 47, -53, 0, 53, 0, 0, 59, 0, -67, 0, 67, -73, 71, 0, -79, 0, 0, 0,
     83, 0, 0, 89, 0, 0, 0, 0, -103, 101, 0, 0, 107, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, -151]
  primes.getD m 0

/-- Form the integral coefficient model from the factorial formula, then remove the content. -/
@[expose] def model (m δ : ℕ) : ℕ × List ℤ :=
  let raw := (List.range (2 * m + 1)).map fun i => (targetCoeff m δ i).num
  let scale := raw.foldl (fun a c => a.gcd c.natAbs) 0
  (scale, raw.map fun c => c / (scale : ℤ))

@[expose] def Valid (m δ : ℕ) (s : ℕ) (l : List ℤ) (p : ℕ) (rev : Bool) : Prop :=
  0 < m ∧ p.Prime ∧ s ≠ 0 ∧ l.length = 2 * m + 1 ∧ l.getD (2 * m) 0 ≠ 0 ∧
  (∀ i : Fin (2 * m + 1), (s : ℚ) * (l.getD i.val 0 : ℚ) = targetCoeff m δ i.val) ∧
  ((Finset.range l.length).gcd fun i => l.getD i 0) = 1 ∧
  (¬ (p : ℤ) ∣ l.getD (if rev then 0 else 2 * m) 0) ∧
  (∀ i : Fin (2 * m), (p : ℤ) ∣ l.getD (if rev then 2 * m - i.val else i.val) 0) ∧
  ¬ (p : ℤ) ^ 2 ∣ l.getD (if rev then 2 * m else 0) 0

private instance (m δ s : ℕ) (l : List ℤ) (p : ℕ) (rev : Bool) :
    Decidable (Valid m δ s l p rev) := by unfold Valid; infer_instance

@[expose] def Cert (m δ : ℕ) : Prop :=
  let w := signedPrime m δ
  let M := model m δ
  Valid m δ M.1 M.2 w.natAbs (decide (w < 0))

private instance (m δ : ℕ) : Decidable (Cert m δ) := by unfold Cert; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the factorial coefficients and divisibility conditions for all 69 pairs.
theorem certificates : ∀ m : Fin 200, ∀ δ : Fin 2,
    m.val ∉ exceptionalIndices δ.val ∨ m.val ∈ remainingIndices δ.val ∨ Cert m.val δ.val := by
  decide +kernel

end EisensteinData

end ArithmeticOfJacobiPolynomials.DerivativeModel
