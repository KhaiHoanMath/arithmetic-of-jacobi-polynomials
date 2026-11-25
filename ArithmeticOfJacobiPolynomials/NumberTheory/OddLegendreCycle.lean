/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.External

/-!
# Lemma 5.11: an odd proper cycle for the Legendre polynomials

For `n ≥ 4` and `ε ∈ {-1, 1}`, with `δ = (ε + 1)/2`, there is a prime `p` with
`2n + δ < p ≤ 4n + ε` (the range of Lemma 5.10) such that
`d = 2n + 1 - (p - ε)/2` is odd and `1 ≤ d < n`. The proof uses the result of Cullinan and
Hajir on primes in both odd classes modulo `4` ([CHL, Lemma 2.2]), taken as the hypothesis
`PrimesModFourInDyadicInterval`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

/-- **Lemma 5.11** (conditional on [CHL, Lemma 2.2]). For `n ≥ 4` and `ε ∈ {-1, 1}` there is a
prime `p ≡ ε (mod 4)` with `2n + δ < p ≤ 4n + ε`, where `δ = (ε + 1)/2`, such that
`d = 2n + 1 - (p - ε)/2` is odd and `1 ≤ d < n`. (The congruence makes the division by `2`
exact.) -/
theorem exists_prime_odd_legendre_cycle (hCHL : PrimesModFourInDyadicInterval) (n : ℕ)
    (hn : 4 ≤ n) (ε : ℤ) (hε : ε = -1 ∨ ε = 1) :
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ≡ ε [ZMOD 4] ∧
      2 * (n : ℤ) + (ε + 1) / 2 < p ∧ (p : ℤ) ≤ 4 * n + ε ∧
      Odd (2 * (n : ℤ) + 1 - (p - ε) / 2) ∧
      1 ≤ 2 * (n : ℤ) + 1 - (p - ε) / 2 ∧ 2 * (n : ℤ) + 1 - (p - ε) / 2 < n := by
  rcases hε with rfl | rfl
  · obtain ⟨p, hp, hp4, hlo', hhi⟩ := hCHL (2 * n + 2) (by omega) 3 (Or.inr rfl)
    have hhi' : p + 1 ≤ 4 * n := by omega
    refine ⟨p, hp, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Int.ModEq]; omega
    · omega
    · omega
    · rw [Int.odd_iff]; omega
    · omega
    · omega
  · obtain ⟨p, hp, hp4, hlo', hhi⟩ := hCHL (2 * n + 4) (by omega) 1 (Or.inl rfl)
    have hhi' : p ≤ 4 * n + 3 := by omega
    refine ⟨p, hp, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Int.ModEq]; omega
    · omega
    · omega
    · rw [Int.odd_iff]; omega
    · omega
    · omega

end ArithmeticOfJacobiPolynomials
