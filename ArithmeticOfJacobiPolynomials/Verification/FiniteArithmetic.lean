module

public import ArithmeticOfJacobiPolynomials.Jacobi.LegendreDerivativeData
public import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# Finite integer comparisons for Legendre polynomials

The first check covers the small degrees in the proof at derivative order zero.
The second is the integer part of Lemma C.2. Both use kernel reduction.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Finset FirstDerivativeCriterion

/-- The product whose logarithm is the truncated prime-power sum for derivative order zero. -/
@[expose] def legendrePrimeProduct (m δ : ℕ) : ℕ :=
  ∏ p ∈ (range (m + 1)).filter Nat.Prime, p ^ Nat.log p (2 * (2 * m + δ) + 1)

private def nearPrime (n : ℕ) : ℕ :=
  ((List.range 8).map (fun i => n + 4 - i)).find? (fun p => decide (p.Prime ∧ p ≠ 2))
    |>.getD 0

private def fitsWindow (n p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ p ≤ n + 4 ∧ n ≤ p + 3

private instance (n p : ℕ) : Decidable (fitsWindow n p) := by
  unfold fitsWindow
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The kernel enumerates 198 positive-index cases and the two boundary cases.
private theorem smallDegrees : ∀ m : Fin 100, ∀ δ : Fin 2,
    m.val = 0 ∨ fitsWindow (2 * m.val + δ.val) (nearPrime (2 * m.val + δ.val)) ∨
    (4 ≤ m.val ∧ 64 * m.val * legendrePrimeProduct m.val δ.val ^ 2 < 16 ^ m.val) := by
  decide +kernel

/-- Every small degree is covered by Holt–Wahab or by the integer form of the exact criterion. -/
theorem legendre_small_degree_cases {m δ : ℕ} (hm : 1 ≤ m) (hm' : m < 100) (hδ : δ ≤ 1) :
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≤ 2 * m + δ + 4 ∧ 2 * m + δ ≤ p + 3) ∨
    (4 ≤ m ∧ 64 * m * legendrePrimeProduct m δ ^ 2 < 16 ^ m) := by
  rcases smallDegrees ⟨m, hm'⟩ ⟨δ, by omega⟩ with h | h | h
  · exact False.elim ((Nat.ne_of_gt hm) h)
  · exact Or.inl ⟨_, h⟩
  · exact Or.inr h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The kernel computes the prime products for the 318 nonexceptional cases.
private theorem firstDerivativeFinite : ∀ m : Fin 200, ∀ δ : Fin 2,
    m.val = 0 ∨ m.val ∈ exceptionalIndices δ.val ∨
    (4 ≤ m.val ∧ 64 * m.val * (m.val + 1) ^ 2 * partZ m.val δ.val ^ 2 *
      partU m.val δ.val ^ 2 < 16 ^ m.val * partV m.val δ.val ^ 2) := by
  simp only [partU_eq, partV_eq, partZ_eq]
  decide +kernel

/-- All 318 strict inequalities in Lemma C.2 follow by integer arithmetic. -/
theorem firstDerivative_integer_inequalities {m δ : ℕ} (hm : 1 ≤ m) (hm' : m ≤ 199)
    (hδ : δ ≤ 1) (he : m ∉ exceptionalIndices δ) :
    4 ≤ m ∧ 64 * m * (m + 1) ^ 2 * partZ m δ ^ 2 * partU m δ ^ 2 <
      16 ^ m * partV m δ ^ 2 := by
  rcases firstDerivativeFinite ⟨m, by omega⟩ ⟨δ, by omega⟩ with h | h | h
  · exact False.elim ((Nat.ne_of_gt hm) h)
  · exact False.elim (he h)
  · exact h

end ArithmeticOfJacobiPolynomials
