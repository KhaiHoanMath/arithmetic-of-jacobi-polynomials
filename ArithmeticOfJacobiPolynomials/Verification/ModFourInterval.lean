module

public import ArithmeticOfJacobiPolynomials.PermGroup.PrimeCriterion
public import ArithmeticOfJacobiPolynomials.Verification.Legendre
import Mathlib.Tactic

/-! # Primes in the two odd residue classes

For integer `x ≥ 9`, each odd class modulo four meets `[x, 2*x-5]`.
Forty primes give a covering for `x < 2000000`. Beyond that point
the manuscript's prime estimate applies with `D = k = 2` and `n = x / 2`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

private def intervalCover (a : ℕ) : List ℕ → ℕ → Bool
  | [], lo => decide (2000000 ≤ lo)
  | p :: ps, lo => decide (p.Prime ∧ p % 4 = a ∧ p + 5 ≤ 2 * lo) && intervalCover a ps (p+1)

private theorem ofIntervalCover {a x : ℕ} (ps : List ℕ) {lo : ℕ}
    (hc : intervalCover a ps lo) (hl : lo ≤ x) (hh : x < 2000000) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = a ∧ x ≤ p ∧ p + 5 ≤ 2 * x := by
  induction ps generalizing lo with
  | nil => simp only [intervalCover, decide_eq_true_eq] at hc; omega
  | cons p ps ih =>
    simp only [intervalCover, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hp, ha, hlow⟩, htail⟩ := hc
    by_cases hxp : x ≤ p
    · exact ⟨p, hp, ha, hxp, by omega⟩
    · exact ih htail (by omega)

private def ones : List ℕ :=
  [13, 17, 29, 53, 101, 197, 389, 773, 1493, 2969, 5897, 11789, 23561, 47093,
   94169, 188333, 376657, 753257, 1506509, 3012949]

private def threes : List ℕ :=
  [11, 19, 31, 59, 107, 211, 419, 827, 1627, 3251, 6491, 12979, 25951, 51899,
   103787, 207563, 415111, 830191, 1660367, 3320699]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The forty primality certificates are checked together.
private theorem bothCovers : intervalCover 1 ones 9 ∧ intervalCover 3 threes 9 := by
  simp only [ones, threes, intervalCover, Bool.and_eq_true, decide_eq_true_eq]
  norm_num

/-- The interval used in Lemma 5.11 follows from the same prime-distribution
input as the prime criterion in Section 5. -/
theorem primesModFourInDyadicInterval_of_BMOR (hBMOR : BMORPrimeCountingBound) :
    PrimesModFourInDyadicInterval := by
  intro x hx a ha
  by_cases hs : x < 2000000
  · rcases ha with rfl | rfl
    · exact ofIntervalCover ones bothCovers.1 hx hs
    · exact ofIntervalCover threes bothCovers.2 hx hs
  have hn : 10 ^ 6 ≤ x / 2 := by change 1000000 ≤ x / 2; omega
  have hg : Int.gcd (a : ℤ) ((2 * 2 : ℕ) : ℤ) = 1 := by rcases ha with rfl | rfl <;> decide
  obtain ⟨p, hlow, hhigh, hp, hres⟩ := exists_prime_lift hBMOR (D := 2) (k := 2)
    (Or.inl rfl) hn (by decide) (by decide) hg
  have hnat : p ≡ a [MOD 4] := Int.natCast_modEq_iff.mp hres
  have ha4 : a < 4 := by omega
  change p % 4 = a % 4 at hnat
  exact ⟨p, hp, hnat.trans (Nat.mod_eq_of_lt ha4), by omega, by omega⟩

/-- Theorem 1.2 with the modulo-four prime interval supplied by the prime-counting bound. -/
theorem legendreGalois_of_prime_bounds (hHW : HoltWahabLegendreIrreducibility)
    (hH : HansonLcmBound) (hZ : JacobiSimpleRealZeros) (hBMOR : BMORPrimeCountingBound)
    (hBT : BrunTitchmarshInequality) (hJones : JonesCycleTheorem)
    (hP : CullinanHajirLegendrePrimeCriterion) (hS : CullinanHajirLegendreSmallDegrees) :
    LegendreGaloisStatement :=
  legendreGalois_of_comparison hHW hH hZ hBMOR hBT hJones hP hS
    (primesModFourInDyadicInterval_of_BMOR hBMOR)

end ArithmeticOfJacobiPolynomials
