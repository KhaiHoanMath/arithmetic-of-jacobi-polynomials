/- Assembled by AxiomProver. -/
module

public import Mathlib.Data.Nat.Prime.Factorial
public import ArithmeticOfJacobiPolynomials.Padic.IntegralLocalBound
public import ArithmeticOfJacobiPolynomials.Analysis.SymmetricRanges

/-!
# The elementary symmetric criterion and the case `r = 1`

Section 3.2 of the manuscript (proof of Theorem 3.4, last paragraph, and the proof of
Theorem 1.5). For integers `r ≥ 0`, `m ≥ 1`, `δ ∈ {0,1}`, put `n = 2m+δ`, `S = 2n+2r+1`,
`M = m+r`, `B = binom(n+r, r)` and `A = (n+r)!² / (n! (n+2r)!)` (`symmetricRatio n r`). Write
`L_p = ⌊log_p S⌋ = Nat.log p S`, `D_p = L_p + v_p(A)` ((3.15)), `Ψ_B(S) = ∑_{p ≤ B} L_p log p` and
`log A_{≤m} = ∑_{p ≤ m} v_p(A) log p`; all sums over primes are written explicitly.

Main results:
* `symmetric_enlarge`: (3.23), in the form
  `∑_{p ≤ m} D_p log p ≤ ∑_{p ≤ M} D_p log p ≤ Ψ_M(S) + ∑_{n < p ≤ n+2r} log p + log A`
  for `m ≥ max{2r, 4}`;
* `log_choose_add_log_symmetricRatio`, `sum_log_prime_Ioc_le_log_choose`:
  `log binom(n+2r, 2r) + log A = 2 log B - log binom(2r, r)`, and every prime in `(n, n+2r]`
  divides `binom(n+2r, 2r)`;
* `symmetric_elementary_bound`, `symmetric_exact_of_elementary` (conditional on
  [Hanson, Theorem 1]): for `M ≥ 9`,
  `Ψ_m(S) + log A_{≤m} ≤ (M + √S) log 3 + 2 log B - log binom(2r, r)`, so that the elementary
  criterion (3.14) implies the exact criterion (3.13);
* `sum_padicValRat_symmetricRatio_one_le`, `first_derivative_exact_criterion_sum`: for `r = 1`,
  `A = (n+1)/(n+2)` and `log A_{≤m} ≤ log(2m+2)`, so (3.13) holds for `r = 1` and `m ≥ 200`.

The nonnegativity of `D_p` for `m < p ≤ M` is proved directly: such a prime satisfies `p > r` and
`p² > n + 2r`, so `v_p(A) = 2⌊(n+r)/p⌋ - ⌊n/p⌋ - ⌊(n+2r)/p⌋ ≥ -1`, while `L_p ≥ 1`. A prime
`p > M` has `2p > n + 2r`, so `v_p(A) = 0` unless `n < p ≤ n + 2r`, where `v_p(A) ≥ -1`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Real Finset

/-! ### Logarithms as sums over primes -/

/-- `log N = ∑_{p ∈ P} v_p(N) log p` for a set `P` of primes containing every prime factor
of `N`. -/
theorem log_natCast_eq_sum_padicValNat (N : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hdvd : ∀ p, p.Prime → p ∣ N → N ≠ 0 → p ∈ P) :
    log (N : ℝ) = ∑ p ∈ P, (padicValNat p N : ℝ) * log p := by
  have hsupp : N.factorization.support ⊆ P := by
    intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    exact hdvd p hp.1 hp.2.1 hp.2.2
  rw [Real.log_nat_eq_sum_factorization,
    Finsupp.sum_of_support_subset _ hsupp _ (fun _ _ => by simp)]
  exact sum_congr rfl fun p hp => by rw [Nat.factorization_def N (hP p hp)]

/-- `log k! = ∑_{p ≤ N} v_p(k!) log p` for `k ≤ N`. -/
theorem log_factorial_eq_sum (k N : ℕ) (hk : k ≤ N) :
    log ((k.factorial : ℕ) : ℝ) = ∑ p ∈ (range (N + 1)).filter Nat.Prime,
      (padicValNat p k.factorial : ℝ) * log p :=
  log_natCast_eq_sum_padicValNat _ _ (fun _ hp => (mem_filter.mp hp).2)
    fun _ hp hd _ => mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le
      (((Nat.Prime.dvd_factorial hp).mp hd).trans hk)), hp⟩

/-! ### Valuations of the factorial ratio -/

/-- `v_p(A) = 2 v_p((n+r)!) - v_p(n!) - v_p((n+2r)!)`. -/
theorem padicValRat_symmetricRatio {p : ℕ} (hp : p.Prime) (n r : ℕ) :
    padicValRat p (symmetricRatio n r) = 2 * (padicValNat p (n + r).factorial : ℤ) -
      padicValNat p n.factorial - padicValNat p (n + 2 * r).factorial := by
  have := Fact.mk hp
  have h1 : ((n + r).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : ((n + 2 * r).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [symmetricRatio_eq, padicValRat.div (pow_ne_zero 2 h1) (mul_ne_zero h2 h3),
    padicValRat.pow, padicValRat.mul h2 h3]
  simp only [padicValRat.of_nat]
  push_cast
  ring

/-- `log A = ∑_{p ≤ n+2r} v_p(A) log p`. -/
theorem log_symmetricRatio (n r : ℕ) :
    log (symmetricRatio n r : ℝ) = ∑ p ∈ (range (n + 2 * r + 1)).filter Nat.Prime,
      (padicValRat p (symmetricRatio n r) : ℝ) * log p := by
  have pos : ∀ k : ℕ, (0 : ℝ) < k.factorial := fun k => by exact_mod_cast Nat.factorial_pos k
  have hcast : (symmetricRatio n r : ℝ) =
      ((n + r).factorial : ℝ) ^ 2 / ((n.factorial : ℝ) * (n + 2 * r).factorial) := by
    rw [symmetricRatio_eq]; push_cast; ring
  rw [hcast, Real.log_div (pow_pos (pos _) 2).ne' (mul_pos (pos _) (pos _)).ne',
    Real.log_mul (pos _).ne' (pos _).ne', Real.log_pow,
    log_factorial_eq_sum (n + r) (n + 2 * r) (by omega),
    log_factorial_eq_sum n (n + 2 * r) (by omega),
    log_factorial_eq_sum (n + 2 * r) (n + 2 * r) le_rfl, mul_sum, ← sum_add_distrib,
    ← sum_sub_distrib]
  refine sum_congr rfl fun p hp => ?_
  rw [padicValRat_symmetricRatio (mem_filter.mp hp).2]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Nat.cast_ofNat]
  ring

/-- Legendre's formula for `k < p²`: `v_p(k!) = ⌊k/p⌋`. -/
theorem padicValNat_factorial_of_lt_sq {p k : ℕ} (hp : p.Prime) (hk : k < p * p) :
    padicValNat p k.factorial = k / p := by
  have := Fact.mk hp
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  have hl : Nat.log p k < 2 := Nat.log_lt_of_lt_pow hk0.ne' (by rw [sq]; exact hk)
  rw [padicValNat_factorial hl]
  change ∑ i ∈ Ico 1 (1 + 1), k / p ^ i = k / p
  rw [Nat.Ico_succ_singleton, sum_singleton, pow_one]

/-- For a prime `p` with `p² > n + 2r`,
`v_p(A) = 2⌊(n+r)/p⌋ - ⌊n/p⌋ - ⌊(n+2r)/p⌋`. -/
theorem padicValRat_symmetricRatio_of_large {p n r : ℕ} (hp : p.Prime)
    (hsq : n + 2 * r < p * p) :
    padicValRat p (symmetricRatio n r) =
      2 * (((n + r) / p : ℕ) : ℤ) - ((n / p : ℕ) : ℤ) - (((n + 2 * r) / p : ℕ) : ℤ) := by
  rw [padicValRat_symmetricRatio hp,
    padicValNat_factorial_of_lt_sq (k := n + r) hp (lt_of_le_of_lt (by omega) hsq),
    padicValNat_factorial_of_lt_sq (k := n) hp (lt_of_le_of_lt (by omega) hsq),
    padicValNat_factorial_of_lt_sq hp hsq]

/-- `⌊(x+r)/p⌋ ≤ ⌊x/p⌋ + 1` for `r < p`. -/
theorem div_add_le_div_add_one {p x r : ℕ} (hp : 0 < p) (hr : r < p) :
    (x + r) / p ≤ x / p + 1 := by
  have h1 := Nat.lt_mul_div_succ x hp
  have h2 : x + r < (x / p + 1 + 1) * p := by nlinarith
  exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hp).2 h2)

/-- For a prime `p > r` with `p² > n + 2r`, `v_p(A) ≥ -1`. -/
theorem neg_one_le_padicValRat_symmetricRatio {p n r : ℕ} (hp : p.Prime) (hpr : r < p)
    (hsq : n + 2 * r < p * p) : -1 ≤ padicValRat p (symmetricRatio n r) := by
  rw [padicValRat_symmetricRatio_of_large hp hsq]
  have hb : n / p ≤ (n + r) / p := Nat.div_le_div_right (by omega)
  have hc : (n + 2 * r) / p ≤ (n + r) / p + 1 := by
    rw [show n + 2 * r = n + r + r by ring]
    exact div_add_le_div_add_one hp.pos hpr
  generalize (n + r) / p = a at *
  generalize n / p = b at *
  generalize (n + 2 * r) / p = c at *
  omega

/-- For a prime `p ≤ n` with `2p > n + 2r`, `v_p(A) = 0`. -/
theorem padicValRat_symmetricRatio_eq_zero {p n r : ℕ} (hp : p.Prime) (hpn : p ≤ n)
    (h2p : n + 2 * r < 2 * p) : padicValRat p (symmetricRatio n r) = 0 := by
  have hsq : n + 2 * r < p * p := lt_of_lt_of_le h2p (Nat.mul_le_mul_right p hp.two_le)
  rw [padicValRat_symmetricRatio_of_large hp hsq]
  have hb : 1 ≤ n / p := (Nat.le_div_iff_mul_le hp.pos).2 (by omega)
  have ha : n / p ≤ (n + r) / p := Nat.div_le_div_right (by omega)
  have hac : (n + r) / p ≤ (n + 2 * r) / p := Nat.div_le_div_right (by omega)
  have hc : (n + 2 * r) / p < 2 := (Nat.div_lt_iff_lt_mul hp.pos).2 (by omega)
  generalize (n + r) / p = a at *
  generalize n / p = b at *
  generalize (n + 2 * r) / p = c at *
  omega

/-! ### (3.23) -/

/-- (3.23) for a general `2m ≤ n ≤ 2m+1`. -/
theorem symmetric_enlarge_of (r m n : ℕ) (hn1 : 2 * m ≤ n) (hn2 : n ≤ 2 * m + 1)
    (hrm : 2 * r ≤ m) (hm : 4 ≤ m) :
    ∑ p ∈ (range (m + 1)).filter Nat.Prime,
        (((Nat.log p (2 * n + 2 * r + 1) : ℕ) : ℝ) +
          (padicValRat p (symmetricRatio n r) : ℝ)) * log p ≤
      ∑ p ∈ (range (m + r + 1)).filter Nat.Prime,
        (((Nat.log p (2 * n + 2 * r + 1) : ℕ) : ℝ) +
          (padicValRat p (symmetricRatio n r) : ℝ)) * log p ∧
    ∑ p ∈ (range (m + r + 1)).filter Nat.Prime,
        (((Nat.log p (2 * n + 2 * r + 1) : ℕ) : ℝ) +
          (padicValRat p (symmetricRatio n r) : ℝ)) * log p ≤
      ∑ p ∈ (range (m + r + 1)).filter Nat.Prime,
          ((Nat.log p (2 * n + 2 * r + 1) : ℕ) : ℝ) * log p +
        ∑ p ∈ (Ioc n (n + 2 * r)).filter Nat.Prime, log (p : ℝ) +
        log (symmetricRatio n r : ℝ) := by
  have hsq : ∀ p, m < p → n + 2 * r < p * p := by
    intro p hp
    have h1 : (m + 1) * (m + 1) ≤ p * p := Nat.mul_le_mul hp hp
    have h4 : 4 * m ≤ m * m := Nat.mul_le_mul_right m hm
    nlinarith
  have hlog : ∀ p : ℕ, p.Prime → 0 ≤ log (p : ℝ) := fun p hp =>
    Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  constructor
  · apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [mem_filter, mem_range] at hp ⊢
      exact ⟨by omega, hp.2⟩
    · intro p hp hnot
      obtain ⟨hpM, hpp⟩ := mem_filter.mp hp
      have hpM := mem_range.mp hpM
      have hmp : m < p := by
        by_contra h
        exact hnot (mem_filter.mpr ⟨mem_range.mpr (by omega), hpp⟩)
      have hL : 1 ≤ Nat.log p (2 * n + 2 * r + 1) := Nat.log_pos hpp.one_lt (by omega)
      have hv := neg_one_le_padicValRat_symmetricRatio hpp (n := n) (by omega) (hsq p hmp)
      refine mul_nonneg ?_ (hlog p hpp)
      have hL' : (1 : ℝ) ≤ (Nat.log p (2 * n + 2 * r + 1) : ℕ) := by exact_mod_cast hL
      have hv' : (-1 : ℝ) ≤ (padicValRat p (symmetricRatio n r) : ℝ) := by exact_mod_cast hv
      linarith
  · simp only [add_mul, sum_add_distrib]
    have hT := log_symmetricRatio n r
    have hsub : (range (m + r + 1)).filter Nat.Prime ⊆
        (range (n + 2 * r + 1)).filter Nat.Prime := by
      intro p hp
      simp only [mem_filter, mem_range] at hp ⊢
      exact ⟨by omega, hp.2⟩
    have hsd : ∑ p ∈ (range (n + 2 * r + 1)).filter Nat.Prime \
          (range (m + r + 1)).filter Nat.Prime,
          (padicValRat p (symmetricRatio n r) : ℝ) * log p +
        ∑ p ∈ (range (m + r + 1)).filter Nat.Prime,
          (padicValRat p (symmetricRatio n r) : ℝ) * log p =
        ∑ p ∈ (range (n + 2 * r + 1)).filter Nat.Prime,
          (padicValRat p (symmetricRatio n r) : ℝ) * log p := sum_sdiff hsub
    have hrest : ∑ p ∈ (range (n + 2 * r + 1)).filter Nat.Prime \
          (range (m + r + 1)).filter Nat.Prime,
          -((padicValRat p (symmetricRatio n r) : ℝ) * log p) ≤
        ∑ p ∈ (Ioc n (n + 2 * r)).filter Nat.Prime, log (p : ℝ) := by
      calc ∑ p ∈ (range (n + 2 * r + 1)).filter Nat.Prime \
              (range (m + r + 1)).filter Nat.Prime,
              -((padicValRat p (symmetricRatio n r) : ℝ) * log p)
          ≤ ∑ p ∈ (range (n + 2 * r + 1)).filter Nat.Prime \
              (range (m + r + 1)).filter Nat.Prime,
              (if p ∈ (Ioc n (n + 2 * r)).filter Nat.Prime then log (p : ℝ) else 0) := by
            refine sum_le_sum fun p hp => ?_
            obtain ⟨hpT, hpM⟩ := mem_sdiff.mp hp
            obtain ⟨hpT, hpp⟩ := mem_filter.mp hpT
            have hpT := mem_range.mp hpT
            have hMp : m + r < p := by
              by_contra h
              exact hpM (mem_filter.mpr ⟨mem_range.mpr (by omega), hpp⟩)
            by_cases hpn : p ≤ n
            · rw [padicValRat_symmetricRatio_eq_zero hpp hpn (by omega)]
              split_ifs <;> simp [hlog p hpp]
            · have hpQ : p ∈ (Ioc n (n + 2 * r)).filter Nat.Prime :=
                mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, by omega⟩, hpp⟩
              simp only [hpQ, ↓reduceIte]
              have hv := neg_one_le_padicValRat_symmetricRatio hpp (n := n) (r := r) (by omega)
                (hsq p (by omega))
              have hv' : (-1 : ℝ) ≤ (padicValRat p (symmetricRatio n r) : ℝ) := by
                exact_mod_cast hv
              nlinarith [hlog p hpp]
        _ = ∑ p ∈ ((range (n + 2 * r + 1)).filter Nat.Prime \
              (range (m + r + 1)).filter Nat.Prime).filter
                (· ∈ (Ioc n (n + 2 * r)).filter Nat.Prime), log (p : ℝ) :=
            (sum_filter _ _).symm
        _ ≤ ∑ p ∈ (Ioc n (n + 2 * r)).filter Nat.Prime, log (p : ℝ) := by
            apply sum_le_sum_of_subset_of_nonneg
            · intro p hp
              exact (mem_filter.mp hp).2
            · intro p hp _
              exact hlog p (mem_filter.mp hp).2
    rw [sum_neg_distrib] at hrest
    linarith

/-- **(3.23)** (§3.2). For `m ≥ max{2r, 4}`, `n = 2m+δ`, `S = 2n+2r+1` and
`M = m+r`, with `D_p = ⌊log_p S⌋ + v_p(A)`:
`∑_{p ≤ m} D_p log p ≤ ∑_{p ≤ M} D_p log p ≤ Ψ_M(S) + ∑_{n < p ≤ n+2r} log p + log A`. -/
theorem symmetric_enlarge (r m δ : ℕ) (hδ : δ ≤ 1) (hrm : 2 * r ≤ m) (hm : 4 ≤ m) :
    ∑ p ∈ (range (m + 1)).filter Nat.Prime,
        (((Nat.log p (2 * (2 * m + δ) + 2 * r + 1) : ℕ) : ℝ) +
          (padicValRat p (symmetricRatio (2 * m + δ) r) : ℝ)) * log p ≤
      ∑ p ∈ (range (m + r + 1)).filter Nat.Prime,
        (((Nat.log p (2 * (2 * m + δ) + 2 * r + 1) : ℕ) : ℝ) +
          (padicValRat p (symmetricRatio (2 * m + δ) r) : ℝ)) * log p ∧
    ∑ p ∈ (range (m + r + 1)).filter Nat.Prime,
        (((Nat.log p (2 * (2 * m + δ) + 2 * r + 1) : ℕ) : ℝ) +
          (padicValRat p (symmetricRatio (2 * m + δ) r) : ℝ)) * log p ≤
      ∑ p ∈ (range (m + r + 1)).filter Nat.Prime,
          ((Nat.log p (2 * (2 * m + δ) + 2 * r + 1) : ℕ) : ℝ) * log p +
        ∑ p ∈ (Ioc (2 * m + δ) (2 * m + δ + 2 * r)).filter Nat.Prime, log (p : ℝ) +
        log (symmetricRatio (2 * m + δ) r : ℝ) :=
  symmetric_enlarge_of r m (2 * m + δ) (by omega) (by omega) hrm hm

/-! ### The binomial identity -/

/-- `log binom(n+2r, 2r) + log A = 2 log binom(n+r, r) - log binom(2r, r)`. -/
theorem log_choose_add_log_symmetricRatio (n r : ℕ) :
    log ((n + 2 * r).choose (2 * r) : ℝ) + log (symmetricRatio n r : ℝ) =
      2 * log ((n + r).choose r : ℝ) - log ((2 * r).choose r : ℝ) := by
  have hC1 := Nat.add_choose_mul_factorial_mul_factorial n (2 * r)
  have hB := Nat.add_choose_mul_factorial_mul_factorial n r
  have hC := Nat.add_choose_mul_factorial_mul_factorial r r
  rw [← two_mul] at hC
  have pos : ∀ k : ℕ, (0 : ℝ) < k.factorial := fun k => by exact_mod_cast Nat.factorial_pos k
  have hC1pos : (0 : ℝ) < ((n + 2 * r).choose (2 * r) : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hBpos : (0 : ℝ) < ((n + r).choose r : ℕ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hCpos : (0 : ℝ) < ((2 * r).choose r : ℕ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hA : (symmetricRatio n r : ℝ) =
      ((n + r).factorial : ℝ) ^ 2 / ((n.factorial : ℝ) * (n + 2 * r).factorial) := by
    rw [symmetricRatio_eq]; push_cast; ring
  have hApos : 0 < (symmetricRatio n r : ℝ) := by
    rw [hA]
    exact div_pos (pow_pos (pos _) 2) (mul_pos (pos _) (pos _))
  have key : ((n + 2 * r).choose (2 * r) : ℝ) * (symmetricRatio n r : ℝ) =
      ((n + r).choose r : ℝ) ^ 2 / ((2 * r).choose r : ℝ) := by
    have e1 : ((n + 2 * r).factorial : ℝ) =
        (n + 2 * r).choose (2 * r) * n.factorial * (2 * r).factorial := by
      exact_mod_cast hC1.symm
    have e2 : ((n + r).factorial : ℝ) = (n + r).choose r * n.factorial * r.factorial := by
      exact_mod_cast hB.symm
    have e3 : ((2 * r).factorial : ℝ) = (2 * r).choose r * r.factorial * r.factorial := by
      exact_mod_cast hC.symm
    rw [hA, e1, e2, e3, ← mul_div_assoc, div_eq_div_iff
      (mul_pos (pos n) (mul_pos (mul_pos hC1pos (pos n))
        (mul_pos (mul_pos hCpos (pos r)) (pos r)))).ne' hCpos.ne']
    ring
  rw [← Real.log_mul hC1pos.ne' hApos.ne', key, Real.log_div (pow_pos hBpos 2).ne' hCpos.ne',
    Real.log_pow]
  push_cast; ring

/-- Every prime in `(n, n+2r]` divides `binom(n+2r, 2r)` (for `2r ≤ n`), so
`∑_{n < p ≤ n+2r} log p ≤ log binom(n+2r, 2r)`. -/
theorem sum_log_prime_Ioc_le_log_choose (n r : ℕ) (hrn : 2 * r ≤ n) :
    ∑ p ∈ (Ioc n (n + 2 * r)).filter Nat.Prime, log (p : ℝ) ≤
      log ((n + 2 * r).choose (2 * r) : ℝ) := by
  have hdvd : (∏ p ∈ (Ioc n (n + 2 * r)).filter Nat.Prime, p) ∣ (n + 2 * r).choose (2 * r) := by
    apply Finset.prod_primes_dvd
    · intro p hp
      exact (mem_filter.mp hp).2.prime
    · intro p hp
      obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
      obtain ⟨h1, h2⟩ := mem_Ioc.mp hpI
      have hd : p ∣ (n + 2 * r).factorial := hpp.dvd_factorial.mpr h2
      rw [← Nat.add_choose_mul_factorial_mul_factorial n (2 * r)] at hd
      rcases hpp.dvd_mul.mp hd with h | h
      · rcases hpp.dvd_mul.mp h with h | h
        · exact h
        · exact absurd (hpp.dvd_factorial.mp h) (by omega)
      · exact absurd (hpp.dvd_factorial.mp h) (by omega)
  have hpos : 0 < ∏ p ∈ (Ioc n (n + 2 * r)).filter Nat.Prime, p :=
    prod_pos fun p hp => (mem_filter.mp hp).2.pos
  have hle := Nat.le_of_dvd (Nat.choose_pos (by omega)) hdvd
  have hcast : ((∏ p ∈ (Ioc n (n + 2 * r)).filter Nat.Prime, p : ℕ) : ℝ) =
      ∏ p ∈ (Ioc n (n + 2 * r)).filter Nat.Prime, (p : ℝ) := Nat.cast_prod _ _
  rw [← Real.log_prod, ← hcast]
  · exact Real.log_le_log (Nat.cast_pos.mpr hpos) (Nat.cast_le.mpr hle)
  · intro p hp
    exact Nat.cast_ne_zero.mpr (mem_filter.mp hp).2.ne_zero

/-! ### Lemma 2.7 in the `Nat.log` form -/

/-- Lemma 2.7, first inequality, with `L_p = Nat.log p S` for a natural number `S`: for `B ≥ 9`
and `1 ≤ S ≤ 5B`, `∑_{p ≤ B} L_p log p ≤ log lcm(1, …, B) + log lcm(1, …, ⌊√S⌋)`. -/
theorem sum_natLog_mul_log_le_log_lcm (B S : ℕ) (hB : 9 ≤ B) (hS1 : 1 ≤ S) (hS : S ≤ 5 * B) :
    ∑ p ∈ (range (B + 1)).filter Nat.Prime, ((Nat.log p S : ℕ) : ℝ) * log p ≤
      log (Nat.lcmUpto B) + log (Nat.lcmUpto ⌊√(S : ℝ)⌋₊) := by
  have hPprime : ∀ p ∈ (range (B + 1)).filter Nat.Prime, p.Prime :=
    fun p hp => (mem_filter.mp hp).2
  have hPle : ∀ p ∈ (range (B + 1)).filter Nat.Prime, p ≤ B := fun p hp =>
    Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hp).1)
  have hkl : ∀ p ∈ (range (B + 1)).filter Nat.Prime,
      Nat.log p S ≤ Nat.log p B + Nat.log p S / 2 := by
    intro p hp
    have hpp := hPprime p hp
    have h1 : p ^ Nat.log p S ≤ S := Nat.pow_log_le_self p (by omega)
    have h2 : B < p ^ (Nat.log p B + 1) := Nat.lt_pow_succ_log_self hpp.one_lt B
    have h3 : 5 ≤ p ^ Nat.log p B := five_le_pow_log hpp (hPle p hp) hB
    have h4 : p ^ Nat.log p S < p ^ (2 * Nat.log p B + 1) := by
      calc p ^ Nat.log p S ≤ 5 * B := h1.trans hS
        _ < 5 * p ^ (Nat.log p B + 1) := by omega
        _ ≤ p ^ Nat.log p B * p ^ (Nat.log p B + 1) := Nat.mul_le_mul_right _ h3
        _ = p ^ (2 * Nat.log p B + 1) := by rw [← pow_add]; ring_nf
    have h5 := (Nat.pow_lt_pow_iff_right hpp.one_lt).mp h4
    omega
  have hjle : ∀ p ∈ (range (B + 1)).filter Nat.Prime,
      p ^ (Nat.log p S / 2) ≤ ⌊√(S : ℝ)⌋₊ := by
    intro p hp
    have hpp := hPprime p hp
    apply Nat.le_floor
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have h1 : p ^ Nat.log p S ≤ S := Nat.pow_log_le_self p (by omega)
    have h2 : (p ^ (Nat.log p S / 2)) ^ 2 ≤ p ^ Nat.log p S := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right hpp.pos (Nat.div_mul_le_self _ _)
    exact_mod_cast h2.trans h1
  have hA := sum_mul_log_le_log_lcmUpTo _ hPprime (fun p => Nat.log p B) B
    fun p _ => Nat.pow_log_le_self p (by omega)
  have hC := sum_mul_log_le_log_lcmUpTo _ hPprime (fun p => Nat.log p S / 2) _ hjle
  calc ∑ p ∈ (range (B + 1)).filter Nat.Prime, ((Nat.log p S : ℕ) : ℝ) * log p
      ≤ ∑ p ∈ (range (B + 1)).filter Nat.Prime,
          (((Nat.log p B : ℕ) : ℝ) * log p + ((Nat.log p S / 2 : ℕ) : ℝ) * log p) := by
        refine sum_le_sum fun p hp => ?_
        have hlog : 0 ≤ log (p : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (hPprime p hp).one_lt.le)
        have h : ((Nat.log p S : ℕ) : ℝ) ≤
            ((Nat.log p B : ℕ) : ℝ) + ((Nat.log p S / 2 : ℕ) : ℝ) := by
          exact_mod_cast hkl p hp
        nlinarith
    _ = ∑ p ∈ (range (B + 1)).filter Nat.Prime, ((Nat.log p B : ℕ) : ℝ) * log p +
          ∑ p ∈ (range (B + 1)).filter Nat.Prime, ((Nat.log p S / 2 : ℕ) : ℝ) * log p :=
        sum_add_distrib
    _ ≤ _ := add_le_add hA hC

/-! ### The elementary criterion -/

/-- **The elementary bound behind (3.14) ⟹ (3.13)** (conditional on [Hanson, Theorem 1]). For
`m ≥ max{2r, 4}` and `M = m + r ≥ 9`, with `n = 2m+δ`, `S = 2n+2r+1`, `B = binom(n+r, r)`:
`Ψ_m(S) + log A_{≤m} ≤ (M + √S) log 3 + 2 log B - log binom(2r, r)`. -/
theorem symmetric_elementary_bound (hH : HansonLcmBound) (r m δ : ℕ) (hδ : δ ≤ 1)
    (hrm : 2 * r ≤ m) (hm : 4 ≤ m) (hM : 9 ≤ m + r) :
    ∑ p ∈ (range (m + 1)).filter Nat.Prime,
        ((Nat.log p (2 * (2 * m + δ) + 2 * r + 1) : ℕ) : ℝ) * log p +
      ∑ p ∈ (range (m + 1)).filter Nat.Prime,
        (padicValRat p (symmetricRatio (2 * m + δ) r) : ℝ) * log p ≤
    ((m : ℝ) + r + √((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ)) * log 3 +
      2 * log ((2 * m + δ + r).choose r : ℝ) - log ((2 * r).choose r : ℝ) := by
  obtain ⟨h1, h2⟩ := symmetric_enlarge r m δ hδ hrm hm
  have hΨ := sum_natLog_mul_log_le_log_lcm (m + r) (2 * (2 * m + δ) + 2 * r + 1) hM
    (by omega) (by omega)
  have hlt := log_lcm_add_log_lcm_lt hH (m + r) (by omega)
    ((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ)
    (by exact_mod_cast (by omega : 1 ≤ 2 * (2 * m + δ) + 2 * r + 1))
  have hc : ((m + r : ℕ) : ℝ) = m + r := by push_cast; ring
  rw [hc] at hlt
  have hQ := sum_log_prime_Ioc_le_log_choose (2 * m + δ) r (by omega)
  have hid := log_choose_add_log_symmetricRatio (2 * m + δ) r
  simp only [add_mul, sum_add_distrib] at h1 h2
  linarith

/-- **The elementary criterion (3.14) implies the exact criterion (3.13)** (conditional on
[Hanson, Theorem 1]), for `m ≥ max{2r, 4}` and `M ≥ 9`, with `K = binom(m+r, r)`. -/
theorem symmetric_exact_of_elementary (hH : HansonLcmBound) (r m δ : ℕ) (hδ : δ ≤ 1)
    (hrm : 2 * r ≤ m) (hm : 4 ≤ m) (hM : 9 ≤ m + r)
    (h : ((m : ℝ) + r + √((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ)) * log 3 +
        log (8 * √(m : ℝ)) + log ((m + r).choose r : ℝ) +
        2 * log ((2 * m + δ + r).choose r : ℝ) - log ((2 * r).choose r : ℝ) < m * log 4) :
    ∑ p ∈ (range (m + 1)).filter Nat.Prime,
        ((Nat.log p (2 * (2 * m + δ) + 2 * r + 1) : ℕ) : ℝ) * log p +
      log (8 * √(m : ℝ)) + log ((m + r).choose r : ℝ) +
      ∑ p ∈ (range (m + 1)).filter Nat.Prime,
        (padicValRat p (symmetricRatio (2 * m + δ) r) : ℝ) * log p < m * log 4 := by
  have := symmetric_elementary_bound hH r m δ hδ hrm hm hM
  linarith

/-! ### The case `r = 1` -/

/-- `A = (n+1)/(n+2)` for `r = 1`. -/
theorem symmetricRatio_one (n : ℕ) :
    symmetricRatio n 1 = ((n + 1 : ℕ) : ℚ) / ((n + 2 : ℕ) : ℚ) := by
  rw [symmetricRatio_eq, show n + 2 * 1 = n + 1 + 1 by ring, Nat.factorial_succ (n + 1),
    Nat.factorial_succ n]
  have h : (0 : ℚ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- For `r = 1`: `log A_{≤m} = ∑_{p ≤ m} v_p((n+1)/(n+2)) log p ≤ log(n+1) ≤ log(2m+2)`. -/
theorem sum_padicValRat_symmetricRatio_one_le (m δ : ℕ) (hδ : δ ≤ 1) :
    ∑ p ∈ (range (m + 1)).filter Nat.Prime,
        (padicValRat p (symmetricRatio (2 * m + δ) 1) : ℝ) * log p ≤
      log (2 * (m : ℝ) + 2) := by
  have hle : ∀ p ∈ (range (m + 1)).filter Nat.Prime,
      (padicValRat p (symmetricRatio (2 * m + δ) 1) : ℝ) * log p ≤
        (padicValNat p (2 * m + δ + 1) : ℝ) * log p := by
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have := Fact.mk hpp
    have hlog : 0 ≤ log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    rw [symmetricRatio_one, padicValRat.div (by positivity) (by positivity)]
    simp only [padicValRat.of_nat, Int.cast_sub, Int.cast_natCast]
    nlinarith [(Nat.cast_nonneg (padicValNat p (2 * m + δ + 2)) : (0 : ℝ) ≤ _)]
  have hsub : (range (m + 1)).filter Nat.Prime ⊆ (range (2 * m + δ + 2)).filter Nat.Prime := by
    intro p hp
    simp only [mem_filter, mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hlogN := log_natCast_eq_sum_padicValNat (2 * m + δ + 1)
    ((range (2 * m + δ + 2)).filter Nat.Prime) (fun _ hp => (mem_filter.mp hp).2)
    fun _ hp hd _ => mem_filter.mpr ⟨mem_range.mpr
      (by have := Nat.le_of_dvd (by omega) hd; omega), hp⟩
  have hδ' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ
  calc ∑ p ∈ (range (m + 1)).filter Nat.Prime,
        (padicValRat p (symmetricRatio (2 * m + δ) 1) : ℝ) * log p
      ≤ ∑ p ∈ (range (m + 1)).filter Nat.Prime,
          (padicValNat p (2 * m + δ + 1) : ℝ) * log p := sum_le_sum hle
    _ ≤ ∑ p ∈ (range (2 * m + δ + 2)).filter Nat.Prime,
          (padicValNat p (2 * m + δ + 1) : ℝ) * log p :=
        sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => mul_nonneg (Nat.cast_nonneg _)
          (Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_lt.le))
    _ = log ((2 * m + δ + 1 : ℕ) : ℝ) := hlogN.symm
    _ ≤ log (2 * (m : ℝ) + 2) :=
        Real.log_le_log (by positivity) (by push_cast; linarith)

/-- **The exact criterion (3.13) for `r = 1`, `m ≥ 200`** (conditional on [Hanson, Theorem 1]),
with `n = 2m+δ`, `S = 2n+3`, `K = m + 1` and `log A_{≤m} = ∑_{p ≤ m} v_p(A) log p`:
`Ψ_m(S) + log(8√m) + log K + log A_{≤m} < m log 4`. -/
theorem first_derivative_exact_criterion_sum (hH : HansonLcmBound) (m δ : ℕ) (hδ : δ ≤ 1)
    (hm : 200 ≤ m) :
    primePowerLogSum m ((2 * (2 * m + δ) + 2 * 1 + 1 : ℕ) : ℝ) + log (8 * √(m : ℝ)) +
        log ((m + 1).choose 1 : ℝ) +
        ∑ p ∈ (range (m + 1)).filter Nat.Prime,
          (padicValRat p (symmetricRatio (2 * m + δ) 1) : ℝ) * log p < m * log 4 := by
  have hs := sum_padicValRat_symmetricRatio_one_le m δ hδ
  have ha : exp (∑ p ∈ (range (m + 1)).filter Nat.Prime,
      (padicValRat p (symmetricRatio (2 * m + δ) 1) : ℝ) * log p) ≤ 2 * m + 2 :=
    (Real.exp_le_exp.mpr hs).trans_eq (Real.exp_log (by positivity))
  have h := first_derivative_exact_criterion hH m δ hδ hm _ (exp_pos _) ha
  rw [Real.log_exp] at h
  rw [show 2 * (2 * m + δ) + 2 * 1 + 1 = 2 * (2 * m + δ) + 3 by ring]
  exact h

end ArithmeticOfJacobiPolynomials
