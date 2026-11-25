module

public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-! # Prime pairs for the Legendre Galois criterion
Cullinan–Hajir, Theorem 1.7, has two alternatives. A fixed prime `q` in the first
alternative works for every `n` from `q + 3` through `2 * q - 2`. Nine degrees in the
negative-sign case use the second alternative.
-/

public section

namespace ArithmeticOfJacobiPolynomials

/-- Check trial divisors in a balanced tree, stopping once the interval starts above √n. -/
private def trial (n : ℕ) : ℕ → ℕ → Bool
  | 0, a => decide (n < a * a ∨ n % a ≠ 0)
  | h + 1, a =>
    decide (n < a * a) || (trial n h a && trial n h (a + 2 ^ h))

private theorem trial_sound (n h : ℕ) {a d : ℕ} (ht : trial n h a = true)
    (ha : a ≤ d) (hd : d < a + 2 ^ h) (hs : d * d ≤ n) : n % d ≠ 0 := by
  induction h generalizing a with
  | zero =>
    simp only [pow_zero] at hd
    have : a = d := by omega
    subst a
    simpa [trial, not_lt.mpr hs] using ht
  | succ h ih =>
    have hstart := (Nat.mul_self_le_mul_self ha).trans hs
    simp only [trial, decide_eq_false (not_lt.mpr hstart), Bool.false_or,
      Bool.and_eq_true] at ht
    rw [pow_succ] at hd
    by_cases hl : d < a + 2 ^ h
    · exact ih ht.1 ha hl
    · exact ih ht.2 (by omega) (by omega)

private def primeCheck (n : ℕ) : Bool :=
  decide (2 ≤ n ∧ n < 65538 * 65538) && trial n 16 2

private theorem prime_of_check {n : ℕ} (hc : primeCheck n = true) : n.Prime := by
  simp only [primeCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  refine Nat.prime_def_le_sqrt.mpr ⟨hc.1.1, fun d hd hds hdiv => ?_⟩
  have hs := Nat.le_sqrt.mp hds
  have htop : d < 65538 := by
    by_contra! h
    have := Nat.mul_self_le_mul_self h
    omega
  exact (trial_sound n 16 hc.2 hd (by norm_num; omega) hs) (Nat.mod_eq_zero_of_dvd hdiv)

private def cover (δ last : ℕ) : List ℕ → ℕ → Bool
  | [], lo => decide (last < lo)
  | q :: qs, lo =>
    (primeCheck q && primeCheck (2 * q + 2*δ-1) && decide (q + 3 ≤ lo ∧ lo + 1 < 2 * q)) &&
      cover δ last qs (2 * q - 1)

private theorem ofCover (δ last n : ℕ) (qs : List ℕ) {lo : ℕ} (h : cover δ last qs lo = true)
    (hlo : lo ≤ n) (hhi : n ≤ last) :
    ∃ q : ℕ, q.Prime ∧ n + 1 < 2 * q ∧ q + 2 < n ∧ (2 * q + 2*δ-1).Prime := by
  induction qs generalizing lo with
  | nil => simp [cover] at h; omega
  | cons q qs ih =>
    simp only [cover, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hq, hp⟩, hqlo, _⟩, htail⟩ := h
    by_cases hcut : n + 1 < 2 * q
    · exact ⟨q, prime_of_check hq, hcut, by omega, prime_of_check hp⟩
    · exact ih htail (by omega)

private def firstPlus : List ℕ :=
  [23, 41, 53, 89, 173, 293, 509, 1013, 2003, 3911, 7691, 15269, 30449, 60779,
   121403, 242681, 485123, 970061, 1940069, 3880091, 7760171, 15520229, 31040231,
   62080313, 124160489, 248320931, 496641683, 993283253]

private def firstMinus : List ℕ :=
  [79, 139, 271, 499, 967, 1867, 3709, 7411, 14737, 29347, 58687, 117361, 234571,
   469009, 937777, 1875541, 3751057, 7501987, 15003421, 30006679, 60013309,
   120026611, 240053131, 480106219, 960212431]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The primality checks in the two long lists reach integers of ten digits.
private theorem covers : cover 1 (10 ^ 9) firstPlus 26 = true ∧
    cover 0 72 [19, 31, 37] 26 = true ∧ cover 0 (10 ^ 9) firstMinus 82 = true := by
  decide +kernel

private def secondWitness (n : ℕ) : ℕ :=
  ([47, 67, 67, 71, 73, 73, 59, 71, 73] : List ℕ)[n - 73]?.getD 0

private theorem secondPairs {n : ℕ} (hl : 73 ≤ n) (hh : n ≤ 81) :
    ∃ q : ℕ, q.Prime ∧ n + 1 < 2 * q ∧ q + 2 < n ∧ (2 * (2 * n + 1 - q) - 1).Prime := by
  refine ⟨secondWitness n, ?_⟩
  interval_cases n <;> decide +kernel

/-- The prime condition of Cullinan–Hajir, Theorem 1.7, in every degree from 26 to a billion.
The sign is `2δ-1`; the inequalities encode `(n + 1)/2 < q < n - 2` without division. -/
theorem legendre_prime_pairs {δ n : ℕ} (hδ : δ ≤ 1) (hl : 26 ≤ n) (hh : n ≤ 10 ^ 9) :
    ∃ q : ℕ, q.Prime ∧ n + 1 < 2 * q ∧ q + 2 < n ∧
      ((2 * q + 2*δ-1).Prime ∨ (2 * (2 * n + 1 - q) + 2*δ-1).Prime) := by
  suffices h : (∃ q : ℕ, q.Prime ∧ n + 1 < 2 * q ∧ q + 2 < n ∧ (2 * q + 2*δ-1).Prime) ∨
      (∃ q : ℕ, q.Prime ∧ n + 1 < 2 * q ∧ q + 2 < n ∧ (2 * (2 * n + 1 - q) + 2*δ-1).Prime) by
    rcases h with ⟨q, hq, ha, hb, hp⟩ | ⟨q, hq, ha, hb, hp⟩
    · exact ⟨q, hq, ha, hb, Or.inl hp⟩
    · exact ⟨q, hq, ha, hb, Or.inr hp⟩
  interval_cases δ
  · by_cases h72 : n ≤ 72
    · exact Or.inl (ofCover 0 72 n _ covers.2.1 hl h72)
    by_cases h82 : 82 ≤ n
    · exact Or.inl (ofCover 0 (10 ^ 9) n _ covers.2.2 h82 hh)
    · exact Or.inr (by simpa using secondPairs (n := n) (by omega) (by omega))
  · exact Or.inl (ofCover 1 (10 ^ 9) n _ covers.1 hl hh)

end ArithmeticOfJacobiPolynomials
