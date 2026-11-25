/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Padic.IntegralLocalBound
public import Mathlib.Data.Nat.Totient
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Two elementary remarks of the manuscript

* `symmetricRatio_le_one`: the factorial ratio `A = (n+r)!²/(n!(n+2r)!)` of (3.12) satisfies
  `A ≤ 1` (remark after (3.12)).
* `sqrt_half_le_totient`: `φ(q) ≥ √(q/2)` for `q ≥ 1` (used in the proof of Theorem 1.6, choice
  of `s_0`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

/-- `(n+r)!² ≤ n! (n+2r)!`. -/
theorem factorial_add_sq_le (n r : ℕ) :
    (n + r).factorial * (n + r).factorial ≤ n.factorial * (n + 2 * r).factorial := by
  have h1 := Nat.factorial_mul_ascFactorial n r
  have h2 := Nat.factorial_mul_ascFactorial (n + r) r
  rw [show n + r + r = n + 2 * r by ring] at h2
  have hle : (n + 1).ascFactorial r ≤ (n + r + 1).ascFactorial r := Nat.ascFactorial_le r (by omega)
  calc (n + r).factorial * (n + r).factorial
      = (n.factorial * (n + 1).ascFactorial r) * (n + r).factorial := by rw [h1]
    _ ≤ (n.factorial * (n + r + 1).ascFactorial r) * (n + r).factorial := by gcongr
    _ = n.factorial * (n + 2 * r).factorial := by rw [← h2]; ring

/-- **`A ≤ 1`** for `A = (n+r)!²/(n!(n+2r)!)`. -/
theorem symmetricRatio_le_one (n r : ℕ) : symmetricRatio n r ≤ 1 := by
  rw [symmetricRatio_eq, div_le_one (by positivity), sq]
  exact_mod_cast factorial_add_sq_le n r

/-- `q ≤ 2 φ(q)²`, and `q ≤ φ(q)²` for odd `q`. -/
theorem le_two_mul_totient_sq (q : ℕ) :
    q ≤ 2 * q.totient ^ 2 ∧ (Odd q → q ≤ q.totient ^ 2) := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => simp
  | prime_pow p k hp hk =>
    have hp' : p.Prime := hp
    rw [Nat.totient_prime_pow hp' hk]
    have hp2 := hp'.two_le
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hpj : 1 ≤ p ^ j := Nat.one_le_pow _ _ (by omega)
    have hsq : (p ^ j * (p - 1)) ^ 2 = p ^ j * (p ^ j * (p - 1) ^ 2) := by ring
    have hodd3 : 3 ≤ p → p ^ (j + 1) ≤ (p ^ j * (p - 1)) ^ 2 := by
      intro h3
      have hq : p ≤ (p - 1) ^ 2 := by
        obtain ⟨t, rfl⟩ : ∃ t, p = t + 3 := ⟨p - 3, by omega⟩
        rw [show t + 3 - 1 = t + 2 by omega]; nlinarith
      rw [hsq, pow_succ]
      exact Nat.mul_le_mul_left _ (le_trans hq (Nat.le_mul_of_pos_left _ (by omega)))
    constructor
    · rcases (show p = 2 ∨ 3 ≤ p by omega) with rfl | h3
      · rw [hsq, pow_succ]
        simp only [Nat.add_one_sub_one, one_pow, mul_one]
        nlinarith
      · exact le_trans (hodd3 h3) (by omega)
    · intro hodd
      rcases (show p = 2 ∨ 3 ≤ p by omega) with rfl | h3
      · exact absurd hodd (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, by omega⟩))
      · exact hodd3 h3
  | coprime a b ha hb hab iha ihb =>
    rw [Nat.totient_mul hab, mul_pow]
    refine ⟨?_, fun hodd => ?_⟩
    · rcases Nat.even_or_odd a with hae | hao
      · have hbo : Odd b := by
          by_contra hbe
          rw [Nat.not_odd_iff_even] at hbe
          have h2 := Nat.dvd_gcd (even_iff_two_dvd.mp hae) (even_iff_two_dvd.mp hbe)
          rw [hab] at h2
          omega
        calc a * b ≤ (2 * a.totient ^ 2) * b.totient ^ 2 := Nat.mul_le_mul iha.1 (ihb.2 hbo)
          _ = _ := by ring
      · calc a * b ≤ a.totient ^ 2 * (2 * b.totient ^ 2) := Nat.mul_le_mul (iha.2 hao) ihb.1
          _ = _ := by ring
    · rw [Nat.odd_mul] at hodd
      exact Nat.mul_le_mul (iha.2 hodd.1) (ihb.2 hodd.2)

/-- **`φ(q) ≥ √(q/2)`** for every natural number `q`. -/
theorem sqrt_half_le_totient (q : ℕ) : Real.sqrt ((q : ℝ) / 2) ≤ q.totient := by
  have h := (le_two_mul_totient_sq q).1
  have h' : (q : ℝ) ≤ 2 * (q.totient : ℝ) ^ 2 := by exact_mod_cast h
  rw [Real.sqrt_le_iff]
  exact ⟨by positivity, by linarith⟩

end ArithmeticOfJacobiPolynomials
