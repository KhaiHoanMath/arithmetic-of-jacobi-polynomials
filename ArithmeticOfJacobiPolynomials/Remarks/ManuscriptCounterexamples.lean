/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Polynomial.FactorDegrees
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Prime

/-!
# Counterexamples to two claims as printed

Lemma C.1 needs positive degree. The primitive polynomial `1` and the
empty set of primes satisfy all printed premises but `1` is a unit over `ℚ`.
The proved positive-degree correction is `irreducible_of_factorDegrees_of_natDegree_eq`.

The prime-interval quotation in the proof of Lemma 5.11 (§5.3) incorrectly
quantifies over real numbers. At `x = 23/2`, `[x, 2*x-5]` contains no prime congruent
to `3` modulo `4`. The proof uses the cited natural-number version.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-- The degree-zero instance of all the printed factor-degree premises is vacuous. -/
theorem factorDegrees_degreeZero_counterexample :
    (1 : ℤ[X]).IsPrimitive ∧ (1 : ℤ[X]).natDegree = 0 ∧
      (∀ p ∈ (∅ : Finset ℕ), p.Prime) ∧
      (∀ p ∈ (∅ : Finset ℕ),
        ((1 : ℤ[X]).map (Int.castRingHom (ZMod p))).natDegree = (1 : ℤ[X]).natDegree) ∧
      (∀ p ∈ (∅ : Finset ℕ), Squarefree ((1 : ℤ[X]).map (Int.castRingHom (ZMod p)))) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ (1 : ℤ[X]).natDegree / 2 →
        ∃ p ∈ (∅ : Finset ℕ), ∃ _ : Fact p.Prime,
          k ∉ subsetSums (factorDegrees p (1 : ℤ[X]))) ∧
      ¬ Irreducible ((1 : ℤ[X]).map (Int.castRingHom ℚ)) := by
  refine ⟨isPrimitive_one, by simp, by simp, by simp, by simp, ?_, by simp⟩
  intro k hk hk'
  simp only [natDegree_one, Nat.zero_div] at hk'
  omega

/-- No prime of residue `3 mod 4` lies in the interval `[23/2, 18]`. -/
theorem primesModFour_realInterval_counterexample :
    (9 : ℝ) ≤ 23 / 2 ∧
      ¬ ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧
        (23 / 2 : ℝ) ≤ p ∧ (p : ℝ) ≤ 2 * (23 / 2) - 5 := by
  constructor
  · norm_num
  · rintro ⟨p, hp, hp4, hlo, hhi⟩
    have hlo' : 12 ≤ p := by
      have : 11 < p := by exact_mod_cast (by linarith : (11 : ℝ) < p)
      omega
    have hhi' : p ≤ 18 := by exact_mod_cast (by linarith : (p : ℝ) ≤ 18)
    have : p = 15 := by omega
    subst p
    norm_num at hp

end ArithmeticOfJacobiPolynomials
